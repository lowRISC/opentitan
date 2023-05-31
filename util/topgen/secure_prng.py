# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generating random variables by using a cryptographically secure PRNG.

A class for generating random numbers and permutations.
This class is based on a cryptographically secure PRNG CTR_DRBG described in
NIST SP 800-90A, section 10.2.1
https://csrc.nist.gov/publications/detail/sp/800-90a/rev-1/final
This PRNG guarantees forward and backward secrecy (PRNG output cannot be
computed from any previous or future outputs) as well as enhanced backward
secrecy (previous PRNG outputs cannot be computed from a compromised
internal state).
"""

import logging as log
import sys
from Crypto.Cipher import AES
from math import ceil as _ceil
from math import log as _log


class secure_prng():

    blocklen = 128
    keylen = 128
    ctr_len = blocklen
    # Specification parameter (for easy comparison, not used in the code):
    #     seedlen = blocklen + keylen = 256

    # Maximal number of requests before reseed is required
    RESEED_MAX = 1 << 48

    # Maximal number of bits per request
    REQ_MAX = 1 << 19

    def __init__(self):
        """Initialize an instance.

        Default state value is 0.
        """

        # A 128 bit PRNG output
        self.returned_bits = []

        # CTR_DRBG Internal state as defined in NIST SP 800-90A, page 50
        # The state consists of:
        #     - The value V of 128 bits
        #     - The value Key of 128 bits
        #     - Reseed counter
        # Administrative information such as security_strength and
        # prediction_resistance_flag are missing in this implementation
        # because they are not used by the consuming application.
        self.V = None
        self.Key = None
        self.reseed_counter = None

    def CTR_DRBG_Update(self, provided_data_0, provided_data_1):
        """The update function

        CTR_DRBG_Update process
        Described in NIST SP 800-90A, page 51
        For convenience, input provided_data is devided in two 128 bit chunks.
        """
        cipher = AES.new(self.Key.to_bytes(16, 'big'), AES.MODE_ECB)

        # Steps 1 and 2
        # Loop in step 2 consists of only 2 iterations, it is unrolled here
        # Note ctr_len = blocklen = 128, Therefore we don't go through steps
        # 2.1.1. and 2.1.2
        pt0 = (self.V + 1) % (1 << self.blocklen)
        pt1 = (self.V + 2) % (1 << self.blocklen)
        ct0 = cipher.encrypt(pt0.to_bytes(16, 'big'))
        ct1 = cipher.encrypt(pt1.to_bytes(16, 'big'))

        # Steps 3, 4, 5, 6 and 7
        self.Key = int.from_bytes(ct0, 'big') ^ provided_data_0
        self.V = int.from_bytes(ct1, 'big') ^ provided_data_1
        del (cipher)

    def CTR_DRBG_Generate(self, requested_number_of_bits):
        """CTR_DRBG_Generate

        CTR_DRBG_Generate process as defined in NIST SP 800-90A, page 55
        Section 10.2.1.5.1
        For simplicity, requested_number_of_bits has to be a multiple of 128.
        additional_input is not provided.
        Output status is not provided. In case of a failure, the function will
        error out.
        """

        # Checks if the PRNG was instantitated before first use.
        if not self.reseed_counter:
            log.error("Seed must be provided before requesting output. " +
                      "Use strong_random.reseed()")
            sys.exit(1)

        # Checks that the requested number of bits is allowed.
        if requested_number_of_bits > self.REQ_MAX:
            log.error("Maximal number of bits per request is %d, but %d was "
                      "requested", self.REQ_MAX, requested_number_of_bits)
            sys.exit(1)

        # Step 1
        if self.reseed_counter > self.RESEED_MAX:
            log.error("Reseed required")
            sys.exit(1)

        if requested_number_of_bits % 128:
            log.error("Requested number of bits must be a multiple of 128.")
            sys.exit(1)

        # Step 2 is not executed because additional_input = 0

        # Step 3
        temp = bytearray(0)

        # Number of iterations of the loop in step 4
        N_iterations = requested_number_of_bits // self.blocklen
        cipher = AES.new(self.Key.to_bytes(16, 'big'), AES.MODE_ECB)

        for i in range(N_iterations):
            # Step 4.1
            # Because ctr_len = blocklen, steps 4.1.1 and 4.1.2 are not executed
            self.V = (self.V + 1) % (1 << self.blocklen)
            # Steps 4.2 and 4.3
            pt = self.V
            ct = cipher.encrypt(pt.to_bytes(16, 'big'))
            # Step 4.3
            temp = temp + ct

        del (cipher)

        # Step 5 is not needed because requested_number_of_bits % 128 == 0

        # Step 6 additional_input = 0
        self.CTR_DRBG_Update(0, 0)

        # Step 7
        self.reseed_counter += 1

        # Step 8
        return (temp)

    def CTR_DRBG_Instantiate(self, entropy_input):
        """ CTR_DRBG_Instantiate

        CTR_DRBG Instantiate process, described in NIST SP 800-90A, page 52
        Section 10.2.1.3.1 Instantiation When a Derivation Function is not used
        entropy_input 256 bits
        personalization_string is empty
        """

        # Steps 1, 2 and 3. Personalization string is empty
        seed_material = entropy_input
        # Step 4
        self.Key = 0
        # Step 5
        self.V = 0
        # Step 6. For convenience we split 256 bit seed_material into two 128b
        # integers.
        L = int.from_bytes(seed_material[0:16], 'big')
        R = int.from_bytes(seed_material[16:32], 'big')
        self.CTR_DRBG_Update(L, R)
        # Step 7
        self.reseed_counter = 1

    def reseed(self, seed):
        """Re-seed PRNG

        Instantiates CTR_DRBG with a 256-bit entropy_input.
        Empties returned_bits list in case that it contains residual numbers
        from previous instantiation.
        """
        if seed == 0:
            entropy_input = seed.to_bytes(32, 'big')
            log.error("ERROR: PRNG seeded with 0.")
            sys.exit(1)
        # Check if the provided seed is at least 32 bytes long.
        elif sys.getsizeof(seed) < sys.getsizeof(1 << 255):
            # Cyclically pad the seed to 256 bits and issue a warning.
            # TODO(#19434): Change this warning into an error once dvsim is
            # modified to always use 256 bit seed (At the moment, it uses
            # 32-bit seed).
            new_seed = seed
            seed_bytes = _ceil(_log(seed + 1, 256))
            while new_seed < (1 << 256):
                new_seed <<= seed_bytes * 8
                new_seed += seed
            new_seed %= (1 << 256)
            log.warning("Seed smaller than 256 bits. CTR_DRBG seeded with: " +
                        hex(new_seed))
            entropy_input = new_seed.to_bytes(32, 'big')
        # Check if the seed is longer than 256 bits. Trim the excess bits and
        # issue a warning if it is.
        elif seed > (1 << 256):
            new_seed = seed % (1 << 256)
            log.warning("Seed longer than 256 bits. CTR_DRBG seeded with: " +
                        hex(new_seed))
            entropy_input = new_seed.to_bytes(32, 'big')
        else:
            entropy_input = seed.to_bytes(32, 'big')
        self.CTR_DRBG_Instantiate(entropy_input)
        self.returned_bits = []

    def fetchbyte(self):
        """Fetches the next byte from the returned_bits.

        Used by getrandbits().
        If the returned_bits are consumed, requests fresh 512 bits from CTR_DRBG
        """

        if not self.returned_bits:
            self.returned_bits = list(self.CTR_DRBG_Generate(512))

        return self.returned_bits.pop(0)

    def getrandbits(self, n_bits):
        """Fetches n_bits next bits from a PRNG.

        """

        bitsleft = n_bits
        R = 0
        while (bitsleft > 0):
            random_byte = int(self.fetchbyte())
            if (bitsleft > 8):
                R = (R << 8) | random_byte
                bitsleft = bitsleft - 8
            else:
                random_byte >>= 8 - bitsleft
                R = (R << bitsleft) | random_byte
                bitsleft = 0
        assert R >= 0
        return (R)

    def randbelow(self, n):
        """Generates a random integer smaller than n.

        Uses getrandbits() to generate enough random bits. Repeats until the
        resulting number is smaller than n. The probability of this is more
        than 50% in each loop iteration.
        The amount of consumed randomness is not fixed.
        """
        length_bits = _ceil(_log(n, 2))
        R = self.getrandbits(length_bits)
        while R >= n:
            R = self.getrandbits(length_bits)
        return (R)

    def shuffle(self, x):
        """Shuffles a list x.

        Uses the Fisher-Yates algorithm.
        Each possible permutation of x is generated with equal probability.
        """

        length_list = len(x)
        for i in reversed(range(length_list)):
            j = self.randbelow(i + 1)
            x[i], x[j] = x[j], x[i]

    def choice(self, x):
        """Randomly chooses an element from a list x.

        Uses randbelow() to select an integer smaller than len(x) and returns
        the corresponding element.
        """

        i = self.randbelow(len(x))
        return (x[i])

    def padded_hex(self, c, length):
        """Convert integer to a hexadecimal string with leading zeros."""
        payload = hex(c)[2:]
        padding = '0' * (length - len(payload))
        return '0x' + padding + payload

    def test_point_gen(self, entropy_input):
        """Generate a test point in NIST format

        Generates data for a unit test.
        1. Reseed CTR_DRBG with entropy_input.
        2. Generate two words of 512 bits
        3. Pack entropy_input, the second generated word and CTR_DRBG internal
        state at each step into a test_point.
        """
        entropy = self.padded_hex(entropy_input, 64)
        self.reseed(entropy_input)
        K0 = self.padded_hex(self.Key, 32)
        V0 = self.padded_hex(self.V, 32)
        # The first generated word is not in the test vectors
        self.getrandbits(512)
        K1 = self.padded_hex(self.Key, 32)
        V1 = self.padded_hex(self.V, 32)
        test_word = self.padded_hex(self.getrandbits(512), 128)
        K2 = self.padded_hex(self.Key, 32)
        V2 = self.padded_hex(self.V, 32)
        test_point = {
            'EntropyInput': entropy,
            'Key_Inst': K0,
            'V_Inst': V0,
            'Key_First': K1,
            'V_First': V1,
            'ReturnedBits': test_word,
            'Key_Second': K2,
            'V_Second': V2}
        return test_point


# ----------------------------------------------------------------------
# Create one instance, and export its methods as module-level functions.
# The functions share state across all uses.

_inst = secure_prng()
reseed = _inst.reseed
fetchbyte = _inst.fetchbyte
getrandbits = _inst.getrandbits
randbelow = _inst.randbelow
shuffle = _inst.shuffle
choice = _inst.choice
test_point_gen = _inst.test_point_gen
