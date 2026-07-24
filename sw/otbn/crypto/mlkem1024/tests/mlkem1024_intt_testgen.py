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
inv_zeta = [pow(z, -1, Q) if z != 0 else 0 for z in zeta]


def mont(a: int, b: int) -> int:
    p = a * b
    z = (2488732927 * (p & 0xFFFFFFFF)) & 0xFFFFFFFF
    res = (p + Q * z) >> 32
    return res


def intt_hw(y: list[int]) -> list[int]:
    f = y[:]
    R = pow(2, 32, Q)
    inv128_mont = (pow(128, -1, Q) * R) % Q

    stages = [
        (2, range(64, 128)),
        (4, range(32, 64)),
        (8, range(16, 32)),
        (16, range(8, 16)),
        (32, range(4, 8)),
        (64, range(2, 4)),
        (128, range(1, 2)),
    ]
    for dist, k_range in stages:
        k_list = list(k_range)
        k_idx = 0
        for start in range(0, N, 2 * dist):
            z_inv = inv_zeta[k_list[k_idx]]
            k_idx += 1
            z_inv_mont = (z_inv * R) % Q
            for j in range(start, start + dist):
                y0 = f[j]
                y1 = f[j + dist]

                f0_new = (y0 + y1) % Q
                u = (y0 + 2 * Q) % Q
                t = (u - y1) % Q
                f1_new = mont(z_inv_mont, t)

                f[j] = f0_new
                f[j + dist] = f1_new

    res = [mont(inv128_mont, c) for c in f]
    return res


def words_to_bytes(words):
    return b"".join(w.to_bytes(4, "little") for w in words)


@testcase
def gen_intt_test(seed: Optional[int] = None):
    if seed is not None:
        random.seed(seed)

    poly_in = [random.randint(0, Q - 1) for _ in range(N)]
    intt_expected = intt_hw(poly_in)

    return {
        "entrypoint": "main",
        "input": {
            "dmem": {
                "_poly_in": itoa_dmem(words_to_bytes(poly_in))
            }
        },
        "output": {
            "dmem": {
                "_poly_out": itoa_dmem(words_to_bytes(intt_expected))
            }
        }
    }


if __name__ == '__main__':
    gen_intt_test()
