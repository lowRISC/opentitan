# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generating random variables by using a cryptographically strong PRNG.

A class for generating random numbers and permutations.
This class is based on a cryptographically secure PRNG fitting into DRG3
requirements of BSI's AIS-31.
This class guarentees forward and backward secrecy (PRNG output cannot be
computed from any previous or future outpus) as well as enhanced backward
secrecy (previous PRNG outputs cannot be computed from a compromised
internal state).
The PRNG consists of the 256-bit internal state, a one-way state-update
function and a one-way output functions.
One-way functions are implemented using Matyas-Meyer-Oseas compression
function with AES-128 as the building block.
"""

from Crypto.Cipher import AES
from math import ceil as _ceil
from math import log as _log


class drg3():

    # Initialization vectors for the one-way functions.
    # PRNG security doesn't depend on the choice of these vectors but it is
    # necessary that they are not equal to each other.
    # These vectors don't need to be kept secret.
    IV_UPDATE_LEFT = int.to_bytes(0, 16, 'little')
    IV_UPDATE_RIGHT = int.to_bytes(2 ** 128 - 1, 16, 'little')
    IV_OUTPUT = int.to_bytes(1, 16, 'little')

    def __init__(self):
        """Initialize an instance.

        Default state value is 0.
        """

        # A 256 bit internal state of the PRNG.
        # For convinience of working with AES, this state is organized as two
        # blocks of 16 bytes.
        self.state_block0 = bytearray(16)
        self.state_block1 = bytearray(16)

        # A 128 bit PRNG output
        self.prng_output = []

        # AES cipher in ECB mode. This cipher is used to implement PRNG
        # state-update function and outpuput function.
        key = bytearray(16)
        self.cipher = AES.new(key, AES.MODE_ECB)

        self.step_prng()

    def one_way(self, initial_vector, block1, block2):
        """One-way compression function

        The Matyas-Meyer-Oseas compression function using AES-128 as the
        building block. This function compresses 32-byte (2 blocks) messages
        into 16-byte hashes.
        """

        H = initial_vector
        # Absorb the first block
        self.cipher.key = H
        H = self.cipher.encrypt(block1)
        H = bytes(H[i] ^ block1[i] for i in range(16))
        # Absorb the second block
        self.cipher.key = H
        H = self.cipher.encrypt(block2)
        H = bytes(H[i] ^ block2[i] for i in range(16))

        return H

    def update_state(self):
        """State-update function

        This function updates a the 256-bit state of the PRNG.
        Each half of the state is updated using a one-way compression function
        that injests the entire state and an initialization vectors.
        """

        left = self.one_way(self.IV_UPDATE_LEFT, self.state_block0, self.state_block1)
        right = self.one_way(self.IV_UPDATE_RIGHT, self.state_block0, self.state_block1)
        self.state_block0 = left
        self.state_block1 = right

    def step_prng(self):
        """Single step of a PRNG/

        Updates PRNG state and generates output.
        Output is generated from the state using a one-way compession function.
        """
        self.update_state()
        prng_output = self.one_way(self.IV_OUTPUT, self.state_block0, self.state_block1)
        self.prng_output = list(prng_output)

    def reseed(self, seed):
        """Re-seed PRNG

        Update PRNG internal state with provided seed and step PRNG once.
        """
        self.state_block0 = seed.to_bytes(16, 'little')
        self.state_block1 = bytearray(16)

        self.step_prng()

    def fetchbyte(self):
        """Fetches the next byte from the prng_output.

        Used by getrandbits().
        If the prng_output is consumed, runs step_prng() to generate another
        16 byte word.
        """

        if not self.prng_output:
            self.step_prng()

        return self.prng_output.pop(0)

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


# ----------------------------------------------------------------------
# Create one instance, and export its methods as module-level functions.
# The functions share state across all uses.

_inst = drg3()
reseed = _inst.reseed
fetchbyte = _inst.fetchbyte
getrandbits = _inst.getrandbits
randbelow = _inst.randbelow
shuffle = _inst.shuffle
choice = _inst.choice
