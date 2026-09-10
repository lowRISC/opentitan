#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.testgen import itoa_dmem, testcase

Q = 3329
N = 256
ZETA_BASE = 17


def bitrev7(n: int) -> int:
    return int(f"{n & 127:07b}"[::-1], 2)


zeta = [pow(ZETA_BASE, bitrev7(i), Q) for i in range(128)]


def mont(a: int, b: int) -> int:
    p = a * b
    z = (2488732927 * (p & 0xFFFFFFFF)) & 0xFFFFFFFF
    res = (p + Q * z) >> 32
    return res


def ntt_hw(f: list[int]) -> list[int]:
    y = f[:]
    k = 1
    for dist in [128, 64, 32, 16, 8, 4, 2]:
        for start in range(0, N, 2 * dist):
            z = zeta[k]
            k += 1
            z_mont = (z * pow(2, 32, Q)) % Q
            for j in range(start, start + dist):
                t = mont(z_mont, y[j + dist])
                u = (y[j] + 2 * Q) % Q
                v = (u - t) % Q
                w0_new = (y[j] + t) % Q
                y[j] = w0_new
                y[j + dist] = v
    return y


def words_to_bytes(words):
    return b"".join(w.to_bytes(4, "little") for w in words)


@testcase
def gen_ntt_test(seed: Optional[int] = None):
    if seed is not None:
        random.seed(seed)

    poly_in = [random.randint(0, Q - 1) for _ in range(N)]
    ntt_expected = ntt_hw(poly_in)

    return {
        "entrypoint": "main",
        "input": {
            "dmem": {
                "_poly_in": itoa_dmem(words_to_bytes(poly_in))
            }
        },
        "output": {
            "dmem": {
                "_poly_out": itoa_dmem(words_to_bytes(ntt_expected))
            }
        }
    }


if __name__ == '__main__':
    gen_ntt_test()
