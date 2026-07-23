#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.testgen import itoa_dmem, testcase

Q = 3329
N = 256
R = pow(2, 32, Q)


def bitrev7(n: int) -> int:
    return int(f"{n & 127:07b}"[::-1], 2)


# FIPS 203 gamma twiddles in Montgomery domain (duplicated for 1024-byte WDR loads)
gamma = [pow(17, 2 * bitrev7(i) + 1, Q) for i in range(128)]
gamma_mont = []
for g in gamma:
    g_m = (g * R) % Q
    gamma_mont.extend([g_m, g_m])


def mont(a: int, b: int) -> int:
    p = a * b
    z = (2488732927 * (p & 0xFFFFFFFF)) & 0xFFFFFFFF
    res = (p + Q * z) >> 32
    return res


def poly_mul_hw(a: list[int], b: list[int], g_mont: list[int] = gamma_mont) -> list[int]:
    res = [0] * N
    for i in range(128):
        a0, a1 = a[2 * i], a[2 * i + 1]
        b0, b1 = b[2 * i], b[2 * i + 1]
        g = g_mont[2 * i]

        c0 = (mont(a0, b0) + mont(mont(a1, b1), g)) % Q
        c1 = (mont(a0, b1) + mont(a1, b0)) % Q

        res[2 * i] = c0
        res[2 * i + 1] = c1
    return res


def words_to_bytes(words):
    return b"".join(w.to_bytes(4, "little") for w in words)


@testcase
def gen_poly_mul_test(seed: Optional[int] = None):
    if seed is not None:
        random.seed(seed)

    poly_a = [random.randint(0, Q - 1) for _ in range(N)]
    poly_b = [random.randint(0, Q - 1) for _ in range(N)]
    expected = poly_mul_hw(poly_a, poly_b)

    return {
        "entrypoint": "main",
        "input": {
            "dmem": {
                "_poly_a": itoa_dmem(words_to_bytes(poly_a)),
                "_poly_b": itoa_dmem(words_to_bytes(poly_b)),
                "_poly_gamma": itoa_dmem(words_to_bytes(gamma_mont)),
            }
        },
        "output": {
            "dmem": {
                "_poly_out": itoa_dmem(words_to_bytes(expected))
            }
        }
    }


if __name__ == '__main__':
    gen_poly_mul_test()
