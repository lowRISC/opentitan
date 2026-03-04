#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.testgen import itoa_dmem, itoa_gpr, testcase


MOD_SIZES = [256, 512, 1024, 2048, 3072, 4096]
WORD_SIZE = 256


@testcase
def gen_mod_f4_test(seed: Optional[int] = None):
    mod_size = MOD_SIZES[random.randint(0, len(MOD_SIZES) - 1)]

    k = mod_size // WORD_SIZE
    b = mod_size // 8

    e = 2**16 + 1

    # Sample x such that gcd(x, F4) == 1.
    x_coprime = 0
    y_coprime = 0
    while True:
        x_coprime = random.randint(2**(mod_size - 1), 2**mod_size - 1)
        y_coprime = x_coprime % e
        if y_coprime != 0:
            break

    # Sample x such that gcd(x, F4) > 1.
    x_multiple = 0
    y_multiple = 0
    while True:
        x_multiple = random.randint(2**(mod_size - 1), 2**mod_size - 1)
        y_multiple = x_multiple % e
        if y_multiple == 0:
            break

    k_bytes = int.to_bytes(k, byteorder='little', length=4)

    x_coprime_bytes = int.to_bytes(x_coprime, byteorder='little', length=b)
    y_coprime_bytes = int.to_bytes(y_coprime, byteorder='little', length=32)

    x_multiple_bytes = int.to_bytes(x_multiple, byteorder='little', length=b)
    y_multiple_bytes = int.to_bytes(y_multiple, byteorder='little', length=32)

    return {
        "entrypoint": "main",
        "input": {
            "regs": {
                "x31": itoa_gpr(k_bytes),
            },
            "dmem": {
                "_mod_f4_x_coprime": itoa_dmem(x_coprime_bytes),
                "_mod_f4_x_multiple": itoa_dmem(x_multiple_bytes),
            }
        },
        "output": {
            "dmem": {
                "_mod_f4_y_coprime": itoa_dmem(y_coprime_bytes),
                "_mod_f4_y_multiple": itoa_dmem(y_multiple_bytes),
            }
        }
    }


if __name__ == '__main__':
    gen_mod_f4_test()
