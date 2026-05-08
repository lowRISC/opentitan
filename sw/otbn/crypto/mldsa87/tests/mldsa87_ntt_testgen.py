#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.testgen import itoa_dmem, testcase

# ML-DSA parameters:
Q = 8380417
N = 256
W = 1753
R = 2**32
R2 = pow(R, 2, Q)
MU = pow(-Q, -1, R)


def mont(x, y):
    '''Montgomery multiplication.'''
    p = x * y
    z = (MU * (p % R)) % R
    z = (p + (Q * z)) >> 32
    if z >= Q:
        z -= Q
    return z


def br(i):
    '''Bit-reversal of an integer.'''
    bits = bin(i & (2**8 - 1))[2:].zfill(8)
    return int(bits[::-1], 2)


# NTT twiddle factors in Montgomery space.
zeta = [mont(pow(W, br(i), Q), R2) for i in range(N)]


def ntt(x):
    '''Number-theoretic transform.'''
    y = x[:]
    k, m = 0, N >> 1
    while m > 0:
        start = 0
        while start < N:
            k = k + 1
            z = zeta[k]
            j = start
            for j in range(start, start + m):
                t = mont(z, y[j + m])
                y[j + m] = (y[j] - t) % Q
                y[j] = (y[j] + t) % Q
            start = m + (j + 1)

        m >>= 1
    return y


@testcase
def gen_ntt_test(seed: Optional[int] = None):
    x = [random.randint(0, Q - 1) for _ in range(N)]
    y = ntt(x)

    x_int, y_int = 0, 0
    for i in range(N - 1, -1, -1):
        x_int = (x_int << 32) | x[i]
        y_int = (y_int << 32) | y[i]

    x_bytes = int.to_bytes(x_int, byteorder='little', length=1024)
    y_bytes = int.to_bytes(y_int, byteorder='little', length=1024)

    return {
        "entrypoint": "main",
        "input": {
            "dmem": {
                "_ntt_x": itoa_dmem(x_bytes)
            }
        },
        "output": {
            "dmem": {
                "_ntt_x": itoa_dmem(y_bytes),
                "_ntt_y": itoa_dmem(y_bytes)
            }
        }
    }


if __name__ == '__main__':
    gen_ntt_test()
