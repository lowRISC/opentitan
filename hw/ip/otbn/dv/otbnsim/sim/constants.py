# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum, unique
import re
from typing import Optional, Tuple


class Cmd(IntEnum):
    '''Permitted values of the CMD register.'''
    EXECUTE = 0xd8
    SEC_WIPE_DMEM = 0xc3
    SEC_WIPE_IMEM = 0x1e
    RESUME = 0xa6


class Status(IntEnum):
    '''Permitted values of the STATUS register.'''
    IDLE = 0x00
    BUSY_EXECUTE = 0x01
    BUSY_SEC_WIPE_DMEM = 0x02
    BUSY_SEC_WIPE_IMEM = 0x03
    BUSY_SEC_WIPE_INT = 0x04
    PAUSED = 0x05
    LOCKED = 0xFF


class ErrBits(IntEnum):
    '''A copy of the list of bits in the ERR_BITS register.'''
    BAD_DATA_ADDR = 1 << 0
    BAD_INSN_ADDR = 1 << 1
    CALL_STACK = 1 << 2
    ILLEGAL_INSN = 1 << 3
    LOOP = 1 << 4
    KEY_INVALID = 1 << 5
    RND_REP_CHK_FAIL = 1 << 6
    RND_FIPS_CHK_FAIL = 1 << 7
    MAI_ERROR = 1 << 8
    IMEM_INTG_VIOLATION = 1 << 16
    DMEM_INTG_VIOLATION = 1 << 17
    REG_INTG_VIOLATION = 1 << 18
    BUS_INTG_VIOLATION = 1 << 19
    BAD_INTERNAL_STATE = 1 << 20
    ILLEGAL_BUS_ACCESS = 1 << 21
    LIFECYCLE_ESCALATION = 1 << 22
    FATAL_SOFTWARE = 1 << 23

    # The errors that make OTBN lock instead of just finishing the operation.
    FATAL_MASK = (IMEM_INTG_VIOLATION | DMEM_INTG_VIOLATION |
                  REG_INTG_VIOLATION | BUS_INTG_VIOLATION | BAD_INTERNAL_STATE |
                  ILLEGAL_BUS_ACCESS | LIFECYCLE_ESCALATION | FATAL_SOFTWARE)

    # Every bit that is defined in the ERR_BITS register.
    MASK = (BAD_DATA_ADDR | BAD_INSN_ADDR | CALL_STACK | ILLEGAL_INSN | LOOP |
            KEY_INVALID | RND_REP_CHK_FAIL | RND_FIPS_CHK_FAIL | MAI_ERROR |
            FATAL_MASK)


class LcTx(IntEnum):
    r'''The same encoding as lc_tx_t in the RTL'''
    ON = 0b0101
    OFF = 0b1010
    INVALID = 0


def read_lc_tx_t(value: int) -> LcTx:
    assert 0 <= value <= 15
    if value == LcTx.ON:
        return LcTx.ON
    elif value == LcTx.OFF:
        return LcTx.OFF
    else:
        return LcTx.INVALID


@unique
class CsrAddrs(IntEnum):
    '''All CSR addresses. Keep in sync with csr.yml'''
    FG0 = 0x7c0
    FG1 = 0x7c1
    FLAGS = 0x7c8
    MOD0 = 0x7d0
    MOD1 = 0x7d1
    MOD2 = 0x7d2
    MOD3 = 0x7d3
    MOD4 = 0x7d4
    MOD5 = 0x7d5
    MOD6 = 0x7d6
    MOD7 = 0x7d7
    RND_PREFETCH = 0x7d8
    KMAC_STATUS = 0x7db
    KMAC_CTRL = 0x7dc
    KMAC_CFG = 0x7dd
    KMAC_STRB = 0x7de
    MAI_CTRL = 0x7e0
    RND = 0xfc0
    URND = 0xfc1
    INSN_CNT = 0xfc3
    MAI_STATUS = 0xfca


@unique
class WsrAddrs(IntEnum):
    '''All WSR addresses. Keep in sync with wsr.yml'''
    MOD = 0
    RND = 1
    URND = 2
    ACC = 3
    KEY_S0_L = 4
    KEY_S0_H = 5
    KEY_S1_L = 6
    KEY_S1_H = 7
    KMAC_DATA_S0 = 8
    KMAC_DATA_S1 = 9
    MAI_RES_S0 = 10
    MAI_RES_S1 = 11
    MAI_IN0_S0 = 12
    MAI_IN0_S1 = 13
    MAI_IN1_S0 = 14
    MAI_IN1_S1 = 15


class Permutation:
    '''A fixed bit permutation with precomputed chunked lookup tables.

    The permutation is computed using `_CHUNK_BITS` wide segments. For each chunk position,
    a table maps every possible chunk value to its contribution to the final permuted output,
    with bits already shifted into their final output positions. Once the permutation tables
    are created, apply() does one lookup and one OR per chunk to compute the final result.
    '''

    _CHUNK_BITS = 16
    _SLICE_DIRECT_MAX = 16

    def __init__(self, num_elems: int, literal: str):
        '''Builds the permutation tables from a SystemVerilog permutation literal.

        Args:
            num_elems: The total number of bits the permutation operates on.
            literal: A SystemVerilog string literal representing the mapping.
        '''
        perm, self._perm_inv = self._decode_literal(num_elems, literal)
        self._n = len(perm)
        self._tables = self._build_tables(perm)

    @staticmethod
    def _decode_literal(num_elems: int, literal: str) -> Tuple[int, ...]:
        '''Parses a SystemVerilog literal and inverts it into an input-to-output mapping.

        The raw SystemVerilog literal encodes the permutation as a packed array where
        the i-th field specifies the source input bit to be routed to output bit i.

        Because the `_build_tables` method groups input bits into chunks, it requires
        the inverse mapping: identifying the destination output bit for a given input bit.
        This method performs that inversion dynamically during parsing.

        Args:
            num_elems: The total number of bits the permutation operates on.
            literal: A SystemVerilog string literal representing the mapping (e.g., "8'h63").

        Returns:
            A tuple of length `num_elems`. The value at index `j` represents the
            destination output bit for input bit `j`.
        '''
        # Compute the width of one element and the corresponding bit mask.
        elem_width = (num_elems - 1).bit_length()
        mask = (1 << elem_width) - 1

        # Drop everything that is not a hex digit and parse as a base-16 integer.
        value = int(re.sub(r"\d+'h|[^0-9a-fA-F]", '', literal), 16)
        assert value.bit_length() <= num_elems * elem_width

        # Build the inverted mapping tuple (input_index -> output_index)
        perm = [-1] * num_elems
        perm_inv = [-1] * num_elems
        for out_bit in range(num_elems):
            in_bit = (value >> (out_bit * elem_width)) & mask
            assert 0 <= in_bit < num_elems
            assert perm[in_bit] == -1
            perm[in_bit] = out_bit
            perm_inv[out_bit] = in_bit

        return tuple(perm), tuple(perm_inv)

    ChunkData = Tuple[int, int, Tuple[int, ...]]

    def _build_tables(self, perm: Tuple[int, ...]) -> Tuple[ChunkData, ...]:
        '''Precomputes the chunked lookup tables used by apply().

        This method slices the input mapping into chunks of `_CHUNK_BITS`. For each
        chunk, it generates a lookup table mapping all possible input values
        (up to 2^_CHUNK_BITS) to their final, pre-shifted output contributions.
        This allows `apply()` to compute the full permutation using just a few array
        lookups and bitwise ORs.

        Args:
            perm: A tuple where the value at index `j` represents the destination
                  output bit for input bit `j`.

        Returns:
            A tuple of `ChunkData` structures. Each `ChunkData` is a 3-element tuple:
                1. lo (int): The starting bit index of this chunk (used for shifting).
                2. chunk_mask (int): The bitmask used to extract this chunk's value.
                3. table (Tuple[int, ...]): The precomputed lookup table mapping
                   the chunk's raw value to its final permuted output contribution.
        '''
        tables = []
        # Process the permutation mapping in blocks of size _CHUNK_BITS.
        for lo in range(0, len(perm), self._CHUNK_BITS):
            chunk_perm = perm[lo:lo + self._CHUNK_BITS]
            chunk_mask = (1 << len(chunk_perm)) - 1
            table = []
            # Calculate the pre-shifted output for every possible value this chunk could hold.
            for chunk_val in range(chunk_mask + 1):
                contribution = 0
                # Loop over each in_bit to out_bit mapping inside the current chunk.
                for in_bit, out_bit in enumerate(chunk_perm):
                    if chunk_val & (1 << in_bit):
                        contribution |= (1 << out_bit)
                table.append(contribution)
            tables.append((lo, chunk_mask, tuple(table)))
        return tuple(tables)

    def apply(self, data: int, num_bits: Optional[int] = None, first_bit: int = 0) -> int:
        '''Permutes the bits of `data` using the precomputed lookup tables.

        The permutation is applied in chunks of `_CHUNK_BITS`. For each chunk, the
        precomputed shifted values are looked up and combined using bitwise ORs to
        construct the full permuted result instantly.

        Args:
            data: The integer value whose bits will be permuted.
            num_bits: The number of bits to return from the final permuted result.
            first_bit: The starting bit index of the output slice to return.

        Returns:
            The permuted integer. If `first_bit` and `num_bits` are specified,
            the returned value represents the slice `output[first_bit : first_bit + num_bits]`,
            right-aligned so that `first_bit` becomes bit 0 of the result.
        '''
        if num_bits is None:
            num_bits = self._n
        assert num_bits <= self._n
        assert data.bit_length() <= self._n
        assert first_bit >= 0
        assert first_bit + num_bits <= self._n

        # Small slice: read only the source bits it needs.
        if num_bits != self._n and num_bits <= self._SLICE_DIRECT_MAX:
            result = 0
            for i in range(num_bits):
                result |= ((data >> self._perm_inv[first_bit + i]) & 1) << i
            return result

        # Apply the permutation across all chunks and merge the results.
        full = 0
        for lo, chunk_mask, table in self._tables:
            full |= table[(data >> lo) & chunk_mask]

        # Return the full result immediately if no slicing was requested.
        if first_bit == 0 and num_bits == self._n:
            return full

        # Shift down to right-align to first_bit, then mask to num_bits length.
        return (full >> first_bit) & ((1 << num_bits) - 1)


# Default permutation for the URND permutation in BN MAC. Given as tuple where each entry gives the
# index of the to be picked element. Keep in sync with otbn_pkg.sv::RndCnstBnMacUrndPermDefault.
BN_MAC_PERMUTATION = Permutation(256, '''
    256'h5883853c_f22faef4_c975ab18_050bfc6b_b9193e1b_450d686e_5de1cdb5_a02a1532,
    256'ha3e9dd76_8278f6d4_33f74bd9_edbabd7f_721c5a4e_0c23a6f0_34a477db_84947998,
    256'h6d0affec_df12e025_0fb41ab3_3bdc90e5_ce279907_91227bf1_e4505bcc_2b4c31be,
    256'h562047c5_9df5fd21_73acadc3_b1438b53_bc8e87a1_d7b02e88_16de0e97_6c354669,
    256'he89657fe_2662402d_03e3a849_1f6ff839_668c5574_54e2bf14_9cbb8dd3_d5d1ea81,
    256'h92c73f60_6402b793_52b68911_5161cb7a_09aacab2_0604865f_4dd8d201_101e08c1,
    256'h7c95a23a_ef177de6_d65c418f_daa96a70_5929c83d_fafb9f37_8a4436af_a5a71d13,
    256'hcf48c07e_42d0eb67_c29b3863_9a28e72c_b880f3ee_9e246571_00c6f9c4_4f305e4a
''')
