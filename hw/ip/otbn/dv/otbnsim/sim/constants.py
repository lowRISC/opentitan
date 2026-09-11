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

    _CHUNK_BITS = 8
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
    def _decode_literal(num_elems: int, literal: str) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
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

# Default permutation applied to the primary URND output, directly after the Bivium PRNG. Given as
# tuple where each entry gives the index of the to be picked element. Keep in sync with
# otbn_pkg.sv::RndCnstUrndPermDefault.
URND_PERMUTATION = Permutation(389, '''
    173'h0978_8cf1d647_48c85a94_0884c1aa_e1b4c286_869b82e2,
    256'hed624787_98726008_460f5dbe_5947d383_33426939_a9968ac9_453142a3_73a555e9,
    256'h2f962b66_2c5885ca_4c8f4b1d_540d58bd_a488a337_318212a1_1b051812_bbc465fd,
    256'h18642ae9_ebe38989_d0ba9d45_f0125834_3506ff9f_2aafc5eb_cda2b854_062169b5,
    256'h932cd5c0_37914c53_2ccc221e_6ce49046_d36ac0f8_4ac10c94_1d0d92c1_d972a0db,
    256'h870e5c6b_6808387f_00029e5b_d2e3fc08_da423b13_b02b3adb_35d27b14_2bca73f1,
    256'h20e2fad6_71568004_69ddb5a4_15b5d114_e4cc1a34_06b97949_ece1b96b_9446103c,
    256'h104e6eea_a254df6a_3e202980_769985a2_9f52474a_a52191a8_3a3d4312_a556c35b,
    256'h628e2a39_0b84d644_988976b0_a7204f44_9b78bdd8_6e8a3e95_2fba18b1_be04a92f,
    256'h60add12e_0a831589_3f41e9da_416e3f2f_0ba586b4_676d7918_b5ab071a_e894c50a,
    256'h6edc2180_9408299a_79781605_b69ec51b_fdd4744b_4217e642_10c516cc_1a7ba683,
    256'h2c61e48d_10f36246_8ee2d181_36087564_a2c13245_733cae48_7a98d62a_d18aa0d0,
    256'h4faf9c19_6ea3f242_e40d2cdb_ae313051_75684460_de994131_3a714af8_6722a7a6,
    256'h71047a06_b215bc6e_eefb0b0a_e8a2782f_e111c7e0_a5ce0820_31cfaa34_72de1f4b
''')

# Default permutation for the URND permutation in MAI, applied on top of URND_PERMUTATION to feed
# the mask accelerator. Given as tuple where each entry gives the index of the to be picked
# element. Keep in sync with otbn_pkg.sv::RndCnstMaiUrndPermDefault.
MAI_URND_PERMUTATION = Permutation(389, '''
    173'h113b_75b40630_bb30dd72_f54be9c3_4625b01b_40a768d1,
    256'haa422858_e28c712b_7aac1117_5dc94024_1d657838_819f2969_1399c966_8e49cc53,
    256'ha35adab0_64898614_88a67384_b8f743c1_b9d44b26_50f0c51f_34a5e7ee_f690bce9,
    256'h5d133e2b_f642a5ac_a7209d30_5517a5ea_b83ccf61_0cc6c609_f41c3b33_4b23d00d,
    256'h707c86fc_6e6649e0_b823c55d_fcab7b87_048db103_f21b3672_b62608a9_63a2ff22,
    256'h264a9774_52d444d6_4d6ca94b_29410e06_771c18a4_16c1b5fa_55a60e32_17a129fa,
    256'h4d35047e_a0588565_f505f1ed_52859d69_e7792a2e_98a7bc27_8ff39225_0a14cb9a,
    256'h0a1c0e64_0819ac16_37b46df8_08ad9a57_0eba3261_e1006a1e_cf5a2ebd_248081fb,
    256'hc5425b21_bc94d16b_61a11935_1c9259c8_6a24029c_048d2728_e00154e2_2e8d799a,
    256'h85829555_ee105c1e_ad608846_29449c40_0900532f_90d4f4ec_af0ac1ad_5325d11c,
    256'hacd07ea4_89ef58ca_6a4c1363_260af536_f9b6ab79_11ac2507_d24596b8_3e892f80,
    256'ha7a0ccdd_b8ec4dc0_6eb1b6e8_52e6f07f_d2ac20c5_c9b2315e_8f222a03_b0f81e20,
    256'ha4b9580e_2418e8b5_c74813e1_14768750_267885b4_9542f237_72b4f2e4_30ca4cd2,
    256'hd2c0e844_c805dc2e_30223335_d3546a50_56eb8beb_edc4c45a_0dcc618a_8d60cab1
''')
