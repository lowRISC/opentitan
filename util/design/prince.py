#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Implementation of PRINCE cipher for use in ROM/FLASH scrambling scripts.'''

from typing import List

PRINCE_SBOX4 = [
    0xb, 0xf, 0x3, 0x2,
    0xa, 0xc, 0x9, 0x1,
    0x6, 0x7, 0x8, 0x0,
    0xe, 0x5, 0xd, 0x4
]

PRINCE_SBOX4_INV = [
    0xb, 0x7, 0x3, 0x2,
    0xf, 0xd, 0x8, 0x9,
    0xa, 0x6, 0x4, 0x0,
    0x5, 0xe, 0xc, 0x1
]

PRINCE_SHIFT_ROWS64 = [
    0x4, 0x9, 0xe, 0x3,
    0x8, 0xd, 0x2, 0x7,
    0xc, 0x1, 0x6, 0xb,
    0x0, 0x5, 0xa, 0xf
]

PRINCE_SHIFT_ROWS64_INV = [
    0xc, 0x9, 0x6, 0x3,
    0x0, 0xd, 0xa, 0x7,
    0x4, 0x1, 0xe, 0xb,
    0x8, 0x5, 0x2, 0xf
]

PRINCE_ROUND_CONSTS = [
    0x0000000000000000,
    0x13198a2e03707344,
    0xa4093822299f31d0,
    0x082efa98ec4e6c89,
    0x452821e638d01377,
    0xbe5466cf34e90c6c,
    0x7ef84f78fd955cb1,
    0x85840851f1ac43aa,
    0xc882d32f25323c54,
    0x64a51195e0e3610d,
    0xd3b5a399ca0c2399,
    0xc0ac29b7c97c50dd
]

PRINCE_SHIFT_ROWS_CONSTS = [0x7bde, 0xbde7, 0xde7b, 0xe7bd]


def sbox(data: int, width: int, coeffs: List[int]) -> int:
    assert 0 <= width
    assert 0 <= data < (1 << width)

    full_mask = (1 << width) - 1
    sbox_mask = (1 << (4 * (width // 4))) - 1

    ret = data & (full_mask & ~sbox_mask)
    for i in range(width // 4):
        nibble = (data >> (4 * i)) & 0xf
        sb_nibble = coeffs[nibble]
        ret |= sb_nibble << (4 * i)

    return ret


def prince_nibble_red16(data: int) -> int:
    assert 0 <= data < (1 << 16)
    nib0 = (data >> 0) & 0xf
    nib1 = (data >> 4) & 0xf
    nib2 = (data >> 8) & 0xf
    nib3 = (data >> 12) & 0xf
    return nib0 ^ nib1 ^ nib2 ^ nib3


def prince_mult_prime(data: int) -> int:
    assert 0 <= data < (1 << 64)
    ret = 0
    for blk_idx in range(4):
        data_hw = (data >> (16 * blk_idx)) & 0xffff
        start_sr_idx = 0 if blk_idx in [0, 3] else 1
        for nibble_idx in range(4):
            sr_idx = (start_sr_idx + 3 - nibble_idx) % 4
            sr_const = PRINCE_SHIFT_ROWS_CONSTS[sr_idx]
            nibble = prince_nibble_red16(data_hw & sr_const)
            ret |= nibble << (16 * blk_idx + 4 * nibble_idx)
    return ret


def prince_shiftrows(data: int, inv: bool) -> int:
    assert 0 <= data < (1 << 64)
    shifts = PRINCE_SHIFT_ROWS64_INV if inv else PRINCE_SHIFT_ROWS64

    ret = 0
    for nibble_idx in range(64 // 4):
        src_nibble_idx = shifts[nibble_idx]
        src_nibble = (data >> (4 * src_nibble_idx)) & 0xf
        ret |= src_nibble << (4 * nibble_idx)
    return ret


def prince_fwd_round(rc: int, key: int, data: int) -> int:
    assert 0 <= rc < (1 << 64)
    assert 0 <= key < (1 << 64)
    assert 0 <= data < (1 << 64)

    data = sbox(data, 64, PRINCE_SBOX4)
    data = prince_mult_prime(data)
    data = prince_shiftrows(data, False)
    data ^= rc
    data ^= key
    return data


def prince_inv_round(rc: int, key: int, data: int) -> int:
    assert 0 <= rc < (1 << 64)
    assert 0 <= key < (1 << 64)
    assert 0 <= data < (1 << 64)

    data ^= key
    data ^= rc
    data = prince_shiftrows(data, True)
    data = prince_mult_prime(data)
    data = sbox(data, 64, PRINCE_SBOX4_INV)
    return data


def prince(data: int, key: int, num_rounds_half: int) -> int:
    '''Run the PRINCE cipher

    This uses the new keyschedule proposed by Dinur in "Cryptanalytic
    Time-Memory-Data Tradeoffs for FX-Constructions with Applications to PRINCE
    and PRIDE".

    '''
    assert 0 <= data < (1 << 64)
    assert 0 <= key < (1 << 128)
    assert 0 <= num_rounds_half <= 5

    k1 = key & ((1 << 64) - 1)
    k0 = key >> 64

    k0_rot1 = ((k0 & 1) << 63) | (k0 >> 1)
    k0_prime = k0_rot1 ^ (k0 >> 63)

    data ^= k0
    data ^= k1
    data ^= PRINCE_ROUND_CONSTS[0]

    for hri in range(num_rounds_half):
        round_idx = 1 + hri
        rc = PRINCE_ROUND_CONSTS[round_idx]
        rk = k0 if round_idx & 1 else k1
        data = prince_fwd_round(rc, rk, data)

    data = sbox(data, 64, PRINCE_SBOX4)
    data = prince_mult_prime(data)
    data = sbox(data, 64, PRINCE_SBOX4_INV)

    for hri in range(num_rounds_half):
        round_idx = 11 - num_rounds_half + hri
        rc = PRINCE_ROUND_CONSTS[round_idx]
        rk = k1 if round_idx & 1 else k0
        data = prince_inv_round(rc, rk, data)

    data ^= PRINCE_ROUND_CONSTS[11]
    data ^= k1

    data ^= k0_prime

    return data
