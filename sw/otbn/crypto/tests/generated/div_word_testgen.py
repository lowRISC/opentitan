#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.testgen import itoa_dmem, itoa_gpr, itoa_wdr, testcase


MOD_SIZES = [512, 1024, 2048, 3072, 4096]
WORD_SIZE = 256


@testcase
def gen_div_word_test(seed: Optional[int] = None):
    mod_size = MOD_SIZES[random.randint(0, len(MOD_SIZES) - 1)]
    x_size = mod_size - WORD_SIZE

    k = mod_size // WORD_SIZE
    b = mod_size // 8

    # Sample numerator x and denimonator y.
    x = random.randint(2**(x_size - 1), 2**x_size - 1)
    y = random.randint(2**(WORD_SIZE - 1), 2**WORD_SIZE - 1)
    y |= 1

    # Make x divisible by y, z = x / y.
    z = x
    x *= y

    y_inv = pow(y, -1, 2**WORD_SIZE)

    k_bytes = int.to_bytes(k, byteorder='little', length=4)

    x_bytes = int.to_bytes(x, byteorder='little', length=b)
    y_bytes = int.to_bytes(y, byteorder='little', length=32)
    z_bytes = int.to_bytes(z, byteorder='little', length=b)
    y_inv_bytes = int.to_bytes(y_inv, byteorder='little', length=32)

    return {
        "entrypoint": "main",
        "input": {
            "regs": {
                "x30": itoa_gpr(k_bytes),
                "w20": itoa_wdr(y_bytes),
                "w21": itoa_wdr(y_inv_bytes),
            },
            "dmem": {
                "_div_x": itoa_dmem(x_bytes),
            }
        },
        "output": {
            "dmem": {
                "_div_x": itoa_dmem(z_bytes),
            }
        }
    }


if __name__ == '__main__':
    gen_div_word_test()
