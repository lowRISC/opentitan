#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Implementation of PRINCE cipher for use in ROM/FLASH scrambling scripts.'''

from typing import Callable, List

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


def prince_no_lookup(data: int, key: int, num_rounds_half: int) -> int:
    """Run the PRINCE cipher, computing step-by-step without any lookup tables.

    This uses the new keyschedule proposed by Dinur in "Cryptanalytic
    Time-Memory-Data Tradeoffs for FX-Constructions with Applications to PRINCE
    and PRIDE".

    Args:
        data: The data word to apply PRINCE64 to.
        key: The key to use for scrambling.
        num_rounds_half: The number of half-rounds of PRINCE64 to apply.

    Returns:
        The result of the PRINCE64 block cipher.
    """
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


# We can achieve faster cipher times by using a T-table implementation, with lookup
# tables mixing S-boxes and diffusion into precomputed lookup tables. This is
# better for a Python implementation with interpreter overhead and no bit-slicing.
def _make_linear_byte_luts(func: Callable[[int], int]) -> list[list[int]]:
    """Construct a list of 8 byte-wise lookup tables for a given linear mapping.

    As long as `func` is linear over GF(2), then it can be expressed as some
    XOR of its inputs without any scalars. In this case, we can split it into
    smaller lookup tables which we then XOR together. The size of these tables
    is arbitrary: bytes are nice to work with and make small 256-entry tables.

    Args:
        func: Some function linear over GF(2).

    Returns:
        A list of 8 tables, where each table maps [0,255] to [0,2^64-1].
    """
    # We can quickly compute the tables by taking advantage of `func`'s
    # linearity, forming a basis vector for each bit and using bottom-up DP.
    basis = [func(1 << i) for i in range(64)]

    tables = []
    for byte_index in range(8):
        table = [0] * 256
        # Base case: table[0] = 0, as 0 is the identity for XOR
        for value in range(1, 256):
            # Get the lowest set bit of `value` via the 2C representation
            low = value & -value
            # Recursive case: `value ^ low` < `value` so this mapping is already computed.
            # Use our linear property to compute `table[value] (where `j` is `byte_index`):
            # tables[j][value] = tables[j][(value ^ low) ^ low]                 [using XOR]
            #                  = func(((value ^ low) << 8j) ^ (low << 8j))      [by definition]
            #                  = func((value ^ low) << 8j) ^ func(low << 8j)    [by linearity]
            #                  = tables[j][value ^ low] ^ func(1 << (8j + t))   [see below]
            #                  = table[value ^ low] ^ basis[8j + t]             [substitution]
            # where `t` is just `low.bit_length() - 1`, i.e. the number of 0 LSBs.
            table[value] = table[value ^ low] ^ basis[8 * byte_index + low.bit_length() - 1]
        tables.append(table)

    return tables


def _pre_compose_sbox(tables: list[list[int]], coefficients: list[int]) -> list[list[int]]:
    """Compose a given S-box with a set of linear byte lookup tables.

    The input S-box is applied at a byte granularity, such that we simply re-index
    the given linear lookup tables to apply the S-box before the linear layer. Note
    that this approach does not work *after* a linear layer, since the output of a
    linear layer may mix several input bytes.

    Args:
        tables: The byte-wise lookup tables corresponding to some linear mapping.
        coefficients: The coefficients of the S-box to apply.

    Returns:
        A list of tables corresponding to a composition with the S-box applied before
        the given linear mapping.
    """
    # We tabulate a byte-wise S-box layer based on the input coefficients.
    sbox8 = [sbox(value, 8, coefficients) for value in range(256)]
    # This S-box layer is then used to re-index each input byte table.
    return [[table[sbox8[value]] for value in range(256)] for table in tables]


def _make_sbox_byte_luts(coefficients: list[int]) -> list[list[int]]:
    """Construct a list of 8 byte-wise lookup tables for an S-box.

    Apply the input S-box at a byte granularity, constructing the lookup table
    for such an S-box and shifting it to the relevant byte for each table.

    Args:
        coefficients: The coefficients of the S-box to apply.

    Returns:
        A list of 8 tables, where each table maps [0,255] to [0,2^64-1].
    """
    return [[sbox(value, 8, coefficients) << (8 * byte_index) for value in range(256)]
            for byte_index in range(8)]


def _apply_luts(tables: list[list[int]], data: int) -> int:
    """Apply a list of 8 byte-wise lookup tables to a 64-bit word.

    Args:
        tables: The byte-wise lookup tables corresponding to some linear mapping.
        data: The 64-bit word to apply the mapping of lookup tables to.

    Returns:
        The result of applying the lookup tables to each byte of the data, and
        then XORing the results together.
    """
    # This is the hot loop for the cipher, so we manually unroll for performance
    t0, t1, t2, t3, t4, t5, t6, t7 = tables
    return (t0[data & 0xff] ^ t1[(data >> 8) & 0xff] ^ t2[(data >> 16) & 0xff] ^
            t3[(data >> 24) & 0xff] ^ t4[(data >> 32) & 0xff] ^
            t5[(data >> 40) & 0xff] ^ t6[(data >> 48) & 0xff] ^ t7[data >> 56])


# Forward round (see `prince_fwd_round`): S (S-box), then M' (mixing matrix), then SR (shift rows)
_FORWARD_LOOKUPS = _pre_compose_sbox(
    _make_linear_byte_luts(lambda x: prince_shiftrows(prince_mult_prime(x), False)), PRINCE_SBOX4
)
# Middle round (see `prince_no_lookup`, between the forward and inverse rounds):
# S, then M', then S^-1 (the inverse S-box, which must be applied separately)
_MIDDLE_LOOKUPS = _pre_compose_sbox(_make_linear_byte_luts(prince_mult_prime), PRINCE_SBOX4)
# Inverse round (see `prince_inv_round`): SR^-1, M' (is its own inverse), S^-1 (again, separate)
_INVERSE_LOOKUPS = _make_linear_byte_luts(lambda x: prince_mult_prime(prince_shiftrows(x, True)))
_SBOX_INVERSE_LOOKUPS = _make_sbox_byte_luts(PRINCE_SBOX4_INV)


def prince(data: int, key: int, num_rounds_half: int) -> int:
    """Run the PRINCE cipher, optimized using a T-table approach.

    This is an optimized implementation of `prince_no_lookup` (which instead computes
    the block cipher step-by-step) using a T-table implementation. The forward half
    and middle rounds merge the S-box with the linear (diffusion) layer. The inverse
    half applies the inverse S-box as a separate lookup, which means this is not
    the fully-merged T-table implementation. This avoids per-key setup and simplifies
    the implementation, but adds an extra lookup per half round (except the last).

    Args:
        data: The data word to apply PRINCE64 to.
        key: The key to use for scrambling.
        num_rounds_half: The number of half-rounds of PRINCE64 to apply.

    Returns:
        The result of the PRINCE64 block cipher.
    """
    assert 0 <= data < (1 << 64)
    assert 0 <= key < (1 << 128)
    assert 0 <= num_rounds_half <= 5

    k1 = key & ((1 << 64) - 1)
    k0 = key >> 64

    k0_rot1 = ((k0 & 1) << 63) | (k0 >> 1)
    k0_prime = k0_rot1 ^ (k0 >> 63)

    data ^= k0 ^ k1 ^ PRINCE_ROUND_CONSTS[0]

    for half_round_index in range(num_rounds_half):
        round_idx = 1 + half_round_index
        rc = PRINCE_ROUND_CONSTS[round_idx]
        rk = k0 if round_idx & 1 else k1
        data = _apply_luts(_FORWARD_LOOKUPS, data) ^ rc ^ rk

    data = _apply_luts(_SBOX_INVERSE_LOOKUPS, _apply_luts(_MIDDLE_LOOKUPS, data))

    for half_round_index in range(num_rounds_half):
        round_idx = 11 - num_rounds_half + half_round_index
        rc = PRINCE_ROUND_CONSTS[round_idx]
        rk = k1 if round_idx & 1 else k0
        data ^= rk ^ rc
        data = _apply_luts(_SBOX_INVERSE_LOOKUPS, _apply_luts(_INVERSE_LOOKUPS, data))

    return data ^ PRINCE_ROUND_CONSTS[11] ^ k1 ^ k0_prime
