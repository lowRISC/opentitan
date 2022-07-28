#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Script for scrambling a ROM image'''

import argparse
import sys
from typing import Dict, List

import hjson  # type: ignore
from Crypto.Hash import cSHAKE256

from mem import MemChunk, MemFile
from util.design.secded_gen import ecc_encode_some  # type: ignore

ROM_BASE_WORD = 0x8000 // 4
ROM_SIZE_WORDS = 8192

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

PRESENT_SBOX4 = [
    0xc, 0x5, 0x6, 0xb,
    0x9, 0x0, 0xa, 0xd,
    0x3, 0xe, 0xf, 0x8,
    0x4, 0x7, 0x1, 0x2
]

PRESENT_SBOX4_INV = [
    0x5, 0xe, 0xf, 0x8,
    0xc, 0x1, 0x2, 0xd,
    0xb, 0x4, 0x6, 0x3,
    0x0, 0x7, 0x9, 0xa
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

_UDict = Dict[object, object]


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


def subst_perm_enc(data: int, key: int, width: int, num_rounds: int) -> int:
    '''A model of prim_subst_perm in encrypt mode'''
    assert 0 <= width
    assert 0 <= data < (1 << width)
    assert 0 <= key < (1 << width)

    full_mask = (1 << width) - 1
    bfly_mask = (1 << (2 * (width // 2))) - 1

    for rnd in range(num_rounds):
        data_xor = data ^ key

        # SBox layer
        data_sbox = sbox(data_xor, width, PRESENT_SBOX4)

        # Reverse the vector
        data_rev = 0
        for i in range(width):
            bit = (data_sbox >> i) & 1
            data_rev |= bit << (width - 1 - i)

        # Butterfly
        data_bfly = data_rev & (full_mask & ~bfly_mask)
        for i in range(width // 2):
            # data_bfly[i] = data_rev[2i]
            bit = (data_rev >> (2 * i)) & 1
            data_bfly |= bit << i
            # data_bfly[width/2 + i] = data_rev[2i+1]
            bit = (data_rev >> (2 * i + 1)) & 1
            data_bfly |= bit << (width // 2 + i)

        data = data_bfly

    return data ^ key


def subst_perm_dec(data: int, key: int, width: int, num_rounds: int) -> int:
    '''A model of prim_subst_perm in decrypt mode'''
    assert 0 <= width
    assert 0 <= data < (1 << width)
    assert 0 <= key < (1 << width)

    full_mask = (1 << width) - 1
    bfly_mask = (1 << (2 * (width // 2))) - 1

    for rnd in range(num_rounds):
        data_xor = data ^ key

        # Butterfly
        data_bfly = data_xor & (full_mask & ~bfly_mask)
        for i in range(width // 2):
            # data_bfly[2i] = data_xor[i]
            bit = (data_xor >> i) & 1
            data_bfly |= bit << (2 * i)
            # data_bfly[2i+1] = data_xor[i + width // 2]
            bit = (data_xor >> (i + width // 2)) & 1
            data_bfly |= bit << (2 * i + 1)

        # Reverse the vector
        data_rev = 0
        for i in range(width):
            bit = (data_bfly >> i) & 1
            data_rev |= bit << (width - 1 - i)

        # Inverse SBox layer
        data = sbox(data_rev, width, PRESENT_SBOX4_INV)

    return data ^ key


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


class Scrambler:
    subst_perm_rounds = 2
    num_rounds_half = 2

    def __init__(self, nonce: int, key: int, rom_size_words: int):
        assert 0 <= nonce < (1 << 64)
        assert 0 <= key < (1 << 128)
        assert 0 < rom_size_words < (1 << 64)

        self.nonce = nonce
        self.key = key
        self.rom_size_words = rom_size_words

        self._addr_width = (rom_size_words - 1).bit_length()

    @staticmethod
    def _get_rom_ctrl(modules: List[object]) -> _UDict:
        rom_ctrls = []  # type: List[_UDict]
        for entry in modules:
            assert isinstance(entry, dict)
            entry_type = entry.get('type')
            assert isinstance(entry_type, str)

            if entry_type == 'rom_ctrl':
                rom_ctrls.append(entry)

        assert len(rom_ctrls) == 1
        return rom_ctrls[0]

    @staticmethod
    def _get_params(module: _UDict) -> Dict[str, _UDict]:
        params = module.get('param_list')
        assert isinstance(params, list)

        named_params = {}  # type: Dict[str, _UDict]
        for param in params:
            name = param.get('name')
            assert isinstance(name, str)
            assert name not in named_params
            named_params[name] = param

        return named_params

    @staticmethod
    def _get_param_value(params: Dict[str, _UDict],
                         name: str,
                         width: int) -> int:
        param = params.get(name)
        assert isinstance(param, dict)

        default = param.get('default')
        assert isinstance(default, str)
        int_val = int(default, 0)
        assert 0 <= int_val < (1 << width)
        return int_val

    @staticmethod
    def from_hjson_path(path: str, rom_size_words: int) -> 'Scrambler':
        assert 0 < rom_size_words

        with open(path) as handle:
            top = hjson.load(handle, use_decimal=True)

        assert isinstance(top, dict)
        modules = top.get('module')
        assert isinstance(modules, list)

        rom_ctrl = Scrambler._get_rom_ctrl(modules)

        params = Scrambler._get_params(rom_ctrl)
        nonce = Scrambler._get_param_value(params, 'RndCnstScrNonce', 64)
        key = Scrambler._get_param_value(params, 'RndCnstScrKey', 128)

        return Scrambler(nonce, key, rom_size_words)

    def flatten(self, mem: MemFile) -> MemFile:
        '''Flatten and pad mem up to the correct size

        This adds 8 trailing zero words as space to store the expected hash.
        These are (obviously!) not the right hash: we inject them properly
        later.

        '''
        digest_size_words = 8
        initial_len = self.rom_size_words - digest_size_words
        seed = self.key + self.nonce

        flattened = mem.flatten(initial_len, seed)
        assert len(flattened.chunks) == 1
        assert len(flattened.chunks[0].words) == initial_len

        # Add the 8 trailing zero words. We do it here, rather than passing
        # rom_size_words to mem.flatten, to make sure that we see the error if
        # mem is too big.
        flattened.chunks[0].words += [0] * digest_size_words

        return flattened

    def get_keystream(self, log_addr: int, width: int) -> int:
        assert (log_addr >> self._addr_width) == 0
        assert 0 < width <= 64

        data_nonce_width = 64 - self._addr_width
        data_scr_nonce = self.nonce & ((1 << data_nonce_width) - 1)
        to_scramble = (data_scr_nonce << self._addr_width) | log_addr
        full_keystream = prince(to_scramble, self.key, self.num_rounds_half)

        return full_keystream & ((1 << width) - 1)

    def addr_sp_enc(self, log_addr: int) -> int:
        assert self._addr_width < 64
        data_nonce_width = 64 - self._addr_width
        addr_scr_nonce = self.nonce >> data_nonce_width
        return subst_perm_enc(log_addr, addr_scr_nonce,
                              self._addr_width, self.subst_perm_rounds)

    def addr_sp_dec(self, phy_addr: int) -> int:
        assert self._addr_width < 64

        data_nonce_width = 64 - self._addr_width
        addr_scr_nonce = self.nonce >> data_nonce_width
        return subst_perm_dec(phy_addr, addr_scr_nonce,
                              self._addr_width, self.subst_perm_rounds)

    def data_sp_enc(self, width: int, data: int) -> int:
        return subst_perm_enc(data, 0, width, self.subst_perm_rounds)

    def data_sp_dec(self, width: int, data: int) -> int:
        return subst_perm_dec(data, 0, width, self.subst_perm_rounds)

    def scramble_word(self, width: int, log_addr: int, clr_data: int) -> int:
        '''Scramble clr_data at the given logical address.'''
        keystream = self.get_keystream(log_addr, width)
        return self.data_sp_enc(width, keystream ^ clr_data)

    def unscramble_word(self, width: int, log_addr: int, scr_data: int) -> int:
        keystream = self.get_keystream(log_addr, width)
        sp_scr_data = self.data_sp_dec(width, scr_data)
        return keystream ^ sp_scr_data

    def scramble(self, mem: MemFile) -> MemFile:
        assert len(mem.chunks) == 1
        assert len(mem.chunks[0].words) == self.rom_size_words

        width = mem.width

        # Write addr_sp, data_sp for the S&P networks for address and data,
        # respectively. Write clr[i] for unscrambled data word i and scr[i] for
        # scrambled data word i. We need to construct scr[0], scr[1], ...,
        # scr[self.rom_size_words].
        #
        # Then, for all i, we have:
        #
        #   clr[i] = PRINCE(i) ^ data_sp_dec(scr[addr_sp_enc(i)])
        #
        # Change coordinates by evaluating at addr_sp_dec(i):
        #
        #   clr[addr_sp_dec(i)] = PRINCE(addr_sp_dec(i)) ^ data_sp_dec(scr[i])
        #
        # so
        #
        #   scr[i] = data_sp_enc(clr[addr_sp_dec(i)] ^ PRINCE(addr_sp_dec(i)))
        #
        # Using the scramble_word helper function, this is:
        #
        #   scr[i] = scramble_word(width, addr_sp_dec(i), clr[addr_sp_dec(i)])

        assert width <= 64

        scrambled = []
        for phy_addr in range(self.rom_size_words):
            log_addr = self.addr_sp_dec(phy_addr)
            assert 0 <= log_addr < self.rom_size_words

            clr_data = mem.chunks[0].words[log_addr]
            assert 0 <= clr_data < (1 << width)

            scrambled.append(self.scramble_word(width, log_addr, clr_data))

        return MemFile(mem.width, [MemChunk(0, scrambled)])

    def add_hash(self, scr_mem: MemFile) -> None:
        '''Calculate and insert a cSHAKE256 hash for scr_mem

        This reads all the scrambled data in logical order, except for the last
        8 words. It then calculates the resulting cSHAKE hash and finally
        inserts that hash (unscrambled) in as the top 8 words.

        '''
        # We only support flat memories of the correct length
        assert len(scr_mem.chunks) == 1
        assert scr_mem.chunks[0].base_addr == 0
        assert len(scr_mem.chunks[0].words) == self.rom_size_words
        assert scr_mem.width == 39

        scr_chunk = scr_mem.chunks[0]

        bytes_per_word = 32 // 8
        num_digest_words = 256 // 32

        # Read out the scrambled data in logical address order
        to_hash = b''
        for log_addr in range(self.rom_size_words - num_digest_words):
            phy_addr = self.addr_sp_enc(log_addr)
            scr_word = scr_chunk.words[phy_addr]
            # Note that a scrambled word with ECC amounts to 39bit. The
            # expression (39 + 7) // 8 calculates the amount of bytes that are
            # required to store these bits.
            to_hash += scr_word.to_bytes((39 + 7) // 8, byteorder='little')

        # Hash it
        hash_obj = cSHAKE256.new(data=to_hash,
                                 custom='ROM_CTRL'.encode('UTF-8'))
        digest_bytes = hash_obj.read(bytes_per_word * num_digest_words)
        digest256 = int.from_bytes(digest_bytes, byteorder='little')

        # Chop the 256-bit digest into 32-bit words. These words should never
        # be read "unscrambled": the rom_ctrl checker reads them raw. We can
        # guarantee this by fiddling around with the top 7 bits (which are
        # otherwise ignored) to ensure that they unscramble to words with
        # invalid ECC checksums.
        mask32 = (1 << 32) - 1
        first_digest_idx = self.rom_size_words - num_digest_words
        for digest_idx in range(num_digest_words):
            log_addr = first_digest_idx + digest_idx
            w32 = (digest256 >> (32 * digest_idx)) & mask32
            found_mismatch = False

            for chk_bits in range(128):
                w39 = w32 | (chk_bits << 32)
                clr39 = self.unscramble_word(39, log_addr, w39)
                clr32 = clr39 & mask32
                exp39 = ecc_encode_some('inv_hsiao', 32, [clr32])[0][0]
                if clr39 != exp39:
                    # The checksum doesn't match. Excellent!
                    found_mismatch = True
                    break

            # Surely at least one of the 128 possible choices of top bits
            # should have given us an invalid checksum.
            assert found_mismatch

            phy_addr = self.addr_sp_enc(log_addr)
            scr_chunk.words[phy_addr] = w32


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('hjson')
    parser.add_argument('infile', type=argparse.FileType('rb'))
    parser.add_argument('outfile', type=argparse.FileType('w'))

    args = parser.parse_args()
    scrambler = Scrambler.from_hjson_path(args.hjson, ROM_SIZE_WORDS)

    # Load the input ELF file
    clr_mem = MemFile.load_elf32(args.infile, 4 * ROM_BASE_WORD)

    # Flatten the file, padding with pseudo-random data and ensuring it's
    # exactly scrambler.rom_size_words words long.
    clr_flat = scrambler.flatten(clr_mem)

    # Extend from 32 bits to 39 by adding Hsiao (39,32) ECC bits.
    clr_flat.add_ecc32()
    assert clr_flat.width == 39

    # Scramble the memory
    scr_mem = scrambler.scramble(clr_flat)

    # Insert the expected hash here to the top 8 words
    scrambler.add_hash(scr_mem)

    # Check for collisions
    collisions = scr_mem.collisions()
    if collisions:
        print('ERROR: This combination of ROM contents and scrambling\n'
              '       key results in one or more collisions where\n'
              '       different addresses have the same data.\n'
              '\n'
              '       Looks like we\'ve been (very) unlucky with the\n'
              '       birthday problem. As a work-around, try again after\n'
              '       generating some different RndCnst* parameters.\n',
              file=sys.stderr)
        print('{} colliding addresses:'.format(len(collisions)),
              file=sys.stderr)
        for addr0, addr1 in collisions:
            print('  {:#010x}, {:#010x}'.format(addr0, addr1),
                  file=sys.stderr)
        return 1

    scr_mem.write_vmem(args.outfile)
    return 0


if __name__ == '__main__':
    sys.exit(main())
