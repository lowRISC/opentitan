#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a Python model of the masked GHASH implementation for AES-GCM to verify functional
# correctness of the masking concept.
#
# Note on endianness and bit ordering: Please note that the Advanced Encryption Standard (AES) FIPS
# Publication 197 available at
# https://www.nist.gov/publications/advanced-encryption-standard-aes (see Section 3.3) defines that
# an input sequence of 128 bits (left most bit is the first one)
#
#   b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 ... b125 b126 b127
#
# is mapped to Bytes as follows
#
#   B0  = {b0   b1   b2   b3   b4   b5   b6   b7  }
#   B1  = {b8   b9   b10  b11  b12  b13  b14  b15 }
#   .
#   B15 = {b120 b121 b122 b123 b124 b125 b126 b127} .
#
# The Galois/Counter Mode of Operation (GCM) specification available at
# https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf (See
# Appendix B) then maps these bytes into an array as follows (left most bit is the MSB):
#
#   /-------- Byte 0 --------\      ...      /-------- Byte 15 -------\
#   b0, b1, b2, ... b5, b6, b7, b8, b9, ..., b119, b120, ... b126, b127
#
# This means the bit order has to reversed before the GF(2^128) multiplication to get an array
# with the actual MSB left and the LSB right, i.e.,
#
#   b127, b126, ... b1, b0
#
# For simplicity, this model exclusively uses this last bit ordering. Intermediate results cannot
# be compared with the test vector data found in the above mentioned specifications.

import random

BIT_WIDTH = 128
POLY = (1 << 128) + (1 << 7) + (1 << 2) + (1 << 1) + 1
NUM_CIPHERTEXTS = 10


def gf2m_mult(a, b):
    result = 0
    for k in range(0, BIT_WIDTH):
        if b & (1 << BIT_WIDTH - 1):
            result = result ^ a
        b = (b << 1) % (1 << BIT_WIDTH)
        result = result << 1
        if result & (1 << BIT_WIDTH):
            result = result ^ POLY
    return result


def ghash(H, S, C):
    intermediate = gf2m_mult(C[0], H)
    for k in range(1, len(C)):  # one less because first above
        intermediate = intermediate ^ C[k]
        intermediate = gf2m_mult(intermediate, H)
    intermediate = intermediate ^ len(C)
    intermediate = gf2m_mult(intermediate, H)
    intermediate = intermediate ^ S
    return intermediate


def ghash_masked(H0, H1, S0, S1, C):
    tmp_upper = 0
    tmp_lower = 0
    # First block
    tmp_upper = C[0] ^ S0
    tmp_lower = C[0] ^ S1
    tmp_upper = gf2m_mult(tmp_upper, H0)
    tmp_lower = gf2m_mult(tmp_lower, H1)
    tmp_upper = tmp_upper ^ gf2m_mult(S0, H0) ^ S0
    tmp_lower = tmp_lower ^ gf2m_mult(S1, H1)
    # Loop over blocks before recombination
    for k in range(1, len(C)):  # one less because first above
        tmp_upper = tmp_upper ^ C[k]
        tmp_upper = tmp_upper ^ tmp_lower
        tmp_lower = gf2m_mult(tmp_upper, H1)  # use before oberwriting!
        tmp_upper = gf2m_mult(tmp_upper, H0)
        tmp_upper = tmp_upper ^ gf2m_mult(S0, H0) ^ S0
        tmp_lower = tmp_lower ^ gf2m_mult(S0, H1)
    # Last block
    tmp_upper = tmp_upper ^ len(C)
    tmp_upper = tmp_upper ^ tmp_lower
    tmp_lower = gf2m_mult(tmp_upper, H1)  # use before oberwriting!
    tmp_upper = gf2m_mult(tmp_upper, H0)
    tmp_upper = tmp_upper ^ gf2m_mult(S0, H0) ^ S0
    tmp_lower = tmp_lower ^ gf2m_mult(S0, H1)
    tmp_upper = tmp_upper ^ tmp_lower
    tmp_upper = tmp_upper ^ S1
    return tmp_upper


if __name__ == '__main__':
    # Create list of ciphertexts
    C = []
    for k in range(0, NUM_CIPHERTEXTS):
        C.append(random.randrange(1 << BIT_WIDTH))
    # Create H and S
    H = random.randrange(1 << BIT_WIDTH)
    S = random.randrange(1 << BIT_WIDTH)
    # Split H and S in shares
    H1 = random.randrange(1 << BIT_WIDTH)
    H0 = H ^ H1
    assert H == H0 ^ H1
    S1 = random.randrange(1 << BIT_WIDTH)
    S0 = S ^ S1
    assert S == S0 ^ S1
    # ghash
    result = ghash(H, S, C)
    # ghash masked
    result_masked = ghash_masked(H0, H1, S0, S1, C)
    # Check result
    assert result == result_masked
    print("r:     " + "{0:b}".format(result))
    print("rm:    " + "{0:b}".format(result_masked))
