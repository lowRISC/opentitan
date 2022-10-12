# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generating random variables by using an entropy buffer.

A class for generating random numbers and permutations, by fetching entropy
from a file.
"""

import logging as log
import sys
from math import ceil as _ceil
from math import log as _log

import numpy as np


class strong_random():

    def __init__(self):
        """Initialize an instance.

        Entropy buffer is empty by default.
        """

        self.buffer = np.array([])
        self.buffername = ""

    def load(self, input_file):
        """Load entropy buffer from an external file.

        Currently only supports numpy array of 8-bit values.
        """

        if self.buffername == input_file:
            log.error("Entropy buffer " + input_file + " can't be loaded twice.")
            sys.exit(1)

        self.buffer = np.loadtxt(input_file)
        self.buffername = input_file

    def size(self):
        """Size of the buffer.
        """

        return np.size(self.buffer)

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

        return (self.buffer.size == 0)

    def fetchbyte(self):
        """Fetches the next byte from the buffer.

        Used by getrandbits().
        If the buffer is already empty, raises an error and exits.
        """

        if self.isempty():
            log.error("Entropy buffer empty.")
            sys.exit(1)
        else:
            random_byte = self.buffer[0]
            self.buffer = np.delete(self.buffer, 0)
            return (random_byte)

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


# ----------------------------------------------------------------------
# Create one instance, and export its methods as module-level functions.
# The functions share state across all uses.

_inst = strong_random()
load = _inst.load
size = _inst.size
isempty = _inst.isempty
printstatus = _inst.printstatus
getrandbits = _inst.getrandbits
randbelow = _inst.randbelow
shuffle = _inst.shuffle
