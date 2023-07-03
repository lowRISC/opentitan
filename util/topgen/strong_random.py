# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generating random variables by using an entropy buffer.

A class for generating random numbers and permutations, by fetching entropy
from a file.
"""

import logging as log
import random
import sys
from math import ceil as _ceil
from math import log as _log


class strong_random():
    # Entropy tests (Tests T1 to T4 [AIS31]) are always performed on the
    # sequences of size 20000 bits.
    # Test descriptions and specifications are given in [AIS31] Section 2.4.3.
    #
    # [AIS31] W. Killmann and W. Schindler, A proposal for: Functionality
    # classes for random number generators, Version 2.0, 2011

    SEQ_SIZE_BITS = 20000
    SEQ_SIZE_BYTES = SEQ_SIZE_BITS // 8

    MONOBIT_THRESHOLD = 346
    # Low and high thresholds for the value of a chi-squared distribution with
    # 15 degrees of freedom. Randomly selected value from this distribution
    # falls outside of this interval with 1 in 1000000 probability.
    POKER_LOW_THRESHOLD = 1.03
    POKER_HIGH_THRESHOLD = 57.4

    RUNS_LOW_THRESHOLD = [2267, 1079, 502, 223, 90, 90]
    RUNS_HIGH_THRESHOLD = [2733, 1421, 748, 402, 223, 223]

    LONG_RUN_THRESHOLD = 34

    def __init__(self):
        """Initialize an instance.

        Entropy buffer is empty by default.
        """

        self.buffer = []
        self.buffername = ""

    def bit_count(self, int_no):
        """Computes Hamming weight of a number."""
        return bin(int_no).count("1")

    def test_monobit(self):
        """ Perform Monobit test on buffered data

        This is T1 test from BSI's AIS 20/31 standard.
        This test measures if the number of ones is within the expected limits.
        """
        n_seq = self.size() // self.SEQ_SIZE_BYTES

        results = []
        for j in range(n_seq):
            n_ones = sum(self.bit_count(i) for i in
                         self.buffer[j * self.SEQ_SIZE_BYTES:
                         (j + 1) * self.SEQ_SIZE_BYTES])
            X = abs(n_ones - self.SEQ_SIZE_BITS // 2)

            results.append(X < self.MONOBIT_THRESHOLD)
        return all(results)

    def test_poker(self):
        """ Perform Poker test on buffered data

        This is T2 test from BSI's AIS 20/31 standard.
        This tests measures if all non-overlapping 4-bit patterns follow
        expected distribution.
        """
        n_seq = self.size() // self.SEQ_SIZE_BYTES
        seq_start = []
        for i in range(n_seq + 1):
            seq_start.append(i * self.SEQ_SIZE_BYTES)

        results = []
        n_blocks = 5000

        for j in range(n_seq):
            n_patterns = [0] * 16
            for i in self.buffer[seq_start[j]: seq_start[j + 1]]:
                n_patterns[i & 0xf] += 1
                n_patterns[i >> 4] += 1
            assert sum(n_patterns) == n_blocks

            X = sum(i * i for i in n_patterns) * 16 / n_blocks - n_blocks
            results.append((X > self.POKER_LOW_THRESHOLD) and
                           (X < self.POKER_HIGH_THRESHOLD))
        return all(results)

    def test_runs(self):
        """ Perform Runs test on buffered data

        This is T3 test from BSI's AIS 20/31 standard.
        """
        n_seq = self.size() // self.SEQ_SIZE_BYTES
        seq_start = []
        for i in range(n_seq + 1):
            seq_start.append(i * self.SEQ_SIZE_BYTES)

        for j in range(n_seq):
            n_runs = [[0 for i in range(6)] for j in range(2)]

            b = ""
            for i in self.buffer[seq_start[j]: seq_start[j + 1]]:
                b = b + format(i, '#010b')[2:]
            assert len(b) == self.SEQ_SIZE_BITS

            current_run_len = 1
            i = 0
            while i < self.SEQ_SIZE_BITS:
                if i == self.SEQ_SIZE_BITS - 1:
                    if current_run_len < 6:
                        n_runs[int(b[i])][current_run_len - 1] += 1
                    else:
                        n_runs[int(b[i])][5] += 1
                elif b[i] != b[i + 1]:
                    if current_run_len < 6:
                        n_runs[int(b[i])][current_run_len - 1] += 1
                    else:
                        n_runs[int(b[i])][5] += 1
                    current_run_len = 1
                else:
                    current_run_len += 1
                i += 1
            # The runs test passes only if all numbers of runs are within
            # specified limits
            for k in range(6):
                lo = self.RUNS_LOW_THRESHOLD[k]
                hi = self.RUNS_HIGH_THRESHOLD[k]
                if not (lo <= n_runs[0][k] <= hi and
                        lo <= n_runs[1][k] <= hi):
                    return False

        return True

    def test_long_run(self):
        """ Perform Runs test on buffered data

        This is T4 test from BSI's AIS 20/31 standard.
        """
        n_seq = self.size() // self.SEQ_SIZE_BYTES
        seq_start = []
        for i in range(n_seq + 1):
            seq_start.append(i * self.SEQ_SIZE_BYTES)

        results = []

        for j in range(n_seq):
            b = ""
            for i in self.buffer[seq_start[j]: seq_start[j + 1]]:
                b = b + format(i, '#010b')[2:]
            assert len(b) == self.SEQ_SIZE_BITS

            current_run_len = 1
            max_run_len = 1
            i = 0
            while i < self.SEQ_SIZE_BITS - 1:
                if b[i] == b[i + 1]:
                    current_run_len += 1
                else:
                    current_run_len = 1
                i += 1
                if max_run_len < current_run_len:
                    max_run_len = current_run_len

            results.append(max_run_len < self.LONG_RUN_THRESHOLD)
        return all(results)

    def load(self, input_file):
        """Load entropy buffer from an external file.

        Currently only supports numpy array of 8-bit values.
        """

        if self.buffername == input_file:
            log.error("Entropy buffer " + input_file +
                      " can't be loaded twice.")
            sys.exit(1)
        # Clear buffer before loading a file.
        self.buffer.clear()
        with open(input_file, 'r') as fp:
            for line in fp:
                x = int(line)
                if x in range(256):
                    self.buffer.append(x)
                else:
                    log.error("Read value not in range 0 - 255.")
                    sys.exit(1)
        # Statistical tests operate on chunks of 20000 bits.
        # In order to test the statistical quality of the loaded buffer,
        # the buffer size must be a multiple of SEQ_SIZE_BYTES bytes.
        if self.size() % self.SEQ_SIZE_BYTES:
            log.error("The file size must be a multiple of 20000 bits.")
            sys.exit(1)
        # Testing statistical quality of the loaded buffer. The quality is
        # sufficient only if all tests pass.
        tests_pass = []
        tests_pass.append(self.test_monobit())
        tests_pass.append(self.test_poker())
        tests_pass.append(self.test_runs())
        tests_pass.append(self.test_long_run())

        tests_fail_message = "Insuficient entropy in the buffer."
        if not tests_pass[0]:
            tests_fail_message += "\nMonobit test fails."
        if not tests_pass[1]:
            tests_fail_message += "\nPoker test fails."
        if not tests_pass[2]:
            tests_fail_message += "\nRuns test fails."
        if not tests_pass[3]:
            tests_fail_message += "\nLong Run test fails."

        if not all(tests_pass):
            log.error(tests_fail_message)
        self.buffername = input_file

    def unsecure_generate_from_seed(self, buffer_size, seed):
        """Load entropy buffer from Python's default RNG.

        This is used when no entropy buffer file is loaded. Currently only
        supports numpy array of 8-bit values.
        """
        self.buffer.clear()
        self.buffername = ""
        random.seed(seed)
        for i in range(buffer_size):
            self.buffer.append(random.getrandbits(8))

    def size(self):
        """Size of the buffer.
        """

        return len(self.buffer)

    def printstatus(self):
        """Prints the number of remaining bytes in the buffer.

        May be useful for testing and debugging.
        """

        if self.isempty():
            print('Buffer is empty.')
        else:
            print("Buffer remaining:", len(self.buffer), "bytes.")

    def isempty(self):
        """Checks if the buffer is empty.
        """

        return (not self.buffer)

    def fetchbyte(self):
        """Fetches the next byte from the buffer.

        Used by getrandbits().
        If the buffer is already empty, raises an error and exits.
        """

        if self.isempty():
            log.error("Entropy buffer empty.")
            sys.exit(1)
        else:
            return self.buffer.pop(0)

    def getrandbits(self, n_bits):
        """Fetches n_bits next bits from a buffer.

        Always fetches a whole number of bytes. Unused bits are discarded.
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

_inst = strong_random()
load = _inst.load
unsecure_generate_from_seed = _inst.unsecure_generate_from_seed
size = _inst.size
isempty = _inst.isempty
printstatus = _inst.printstatus
getrandbits = _inst.getrandbits
randbelow = _inst.randbelow
shuffle = _inst.shuffle
choice = _inst.choice
