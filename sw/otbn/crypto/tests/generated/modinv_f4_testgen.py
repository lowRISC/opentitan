#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.testgen import itoa_dmem, itoa_gpr, testcase


MOD_SIZES = [512, 1024, 2048, 3072, 4096]
WORD_SIZE = 256


@testcase
def gen_modinv_f4_test(seed: Optional[int] = None):
    mod_size = MOD_SIZES[random.randint(0, len(MOD_SIZES) - 1)]

    k = mod_size // WORD_SIZE
    b = mod_size // 8

    lmbd = random.randint(2**(mod_size - 1), 2**mod_size - 1)
    lmbd = lmbd >> 1
    lmbd = lmbd << 1

    e = 2**16 + 1
    einv = pow(e, -1, lmbd)

    k_bytes = int.to_bytes(k, byteorder='little', length=4)

    lmbd_bytes = int.to_bytes(lmbd, byteorder='little', length=b)
    einv_bytes = int.to_bytes(einv, byteorder='little', length=b)

    return {
        "entrypoint": "main",
        "input": {
            "regs": {
                "x30": itoa_gpr(k_bytes),
            },
            "dmem": {
                "_modinv_f4_lambda": itoa_dmem(lmbd_bytes),
            }
        },
        "output": {
            "dmem": {
                "_modinv_f4_einv": itoa_dmem(einv_bytes),
            }
        }
    }


if __name__ == '__main__':
    gen_modinv_f4_test()
