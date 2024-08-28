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
from util.design.prince import prince, sbox  # type: ignore
from util.design.secded_gen import ecc_encode_some  # type: ignore
from util.design.secded_gen import load_secded_config


class MemCtrlParams:
    def __init__(
            self, ctrl_name: str,
            memory_type: str,
            module_type: str,
            scr_key: str, scr_key_width: int,
            nonce: str, nonce_width: int
    ):
        '''A memory controller parameters constructor

        @ctrl_name is the memory controller IP block name (e.g. 'rom_ctrl0' for the base ROM)
        @memory_type is the memory type this memory controller run ('rom' or 'ram')
        @module_type is the HJSON module type for this memory controller (e.g. 'rom_ctrl')
        @scr_key is the scrambling key entry name in the HJSON file
        @scr_key_width is the expected scrambling key width
        @nonce is the nonce entry name in the HJSON file
        @nonce_width is the expected nonce width
        '''

        self.ctrl_name = ctrl_name
        self.memory_type = memory_type
        self.module_type = module_type
        self.scr_key = scr_key
        self.scr_key_width = scr_key_width
        self.nonce = nonce
        self.nonce_width = nonce_width


def mem_ctrl_params(mode: str) -> MemCtrlParams:
    return {
        'base-rom': MemCtrlParams('rom_ctrl0',
                                  'rom', 'rom_ctrl',
                                  'RndCnstScrKey', 128,
                                  'RndCnstScrNonce', 64),
        'second-rom': MemCtrlParams('rom_ctrl1',
                                    'rom', 'rom_ctrl',
                                    'RndCnstScrKey', 128,
                                    'RndCnstScrNonce', 64),
        'sram': MemCtrlParams('sram_ctrl_main',
                              'ram', 'sram_ctrl',
                              'RndCnstSramKey', 128,
                              'RndCnstramNonce', 128),
    }[mode]


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

_UDict = Dict[object, object]


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


class Scrambler:
    subst_perm_rounds = 2
    num_rounds_half = 2

    def __init__(self, nonce: int, key: int, rom_base: int, rom_size_words: int):
        assert 0 <= nonce < (1 << 64)
        assert 0 <= key < (1 << 128)
        assert 0 < rom_size_words < (1 << 64)

        self.nonce = nonce
        self.key = key
        self.rom_size_words = rom_size_words
        self.rom_base = rom_base

        self.config = load_secded_config()

        self._addr_width = (rom_size_words - 1).bit_length()

    @staticmethod
    def _get_mem_ctrl(modules: List[object], type: str, name: str) -> _UDict:
        mem_ctrls = []  # type: List[_UDict]
        for entry in modules:
            assert isinstance(entry, dict)
            entry_type = entry.get('type')
            assert isinstance(entry_type, str)

            entry_name = entry.get('name')
            assert isinstance(entry_name, str)

            if entry_type == type and entry_name == name:
                mem_ctrls.append(entry)

        assert len(mem_ctrls) == 1
        return mem_ctrls[0]

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
    def _get_param_value(params: Dict[str, _UDict], name: str,
                         width: int) -> int:
        param = params.get(name)
        assert isinstance(param, dict)

        default = param.get('default')
        assert isinstance(default, str)
        int_val = int(default, 0)
        assert 0 <= int_val < (1 << width)
        return int_val

    @staticmethod
    def _get_size_words(module: _UDict, memory_type: str) -> int:
        memory = module.get("memory")
        assert isinstance(memory, dict)

        memory = memory.get(memory_type)
        assert isinstance(memory, dict)

        size_words_bytes_str = memory.get("size")
        assert isinstance(size_words_bytes_str, str)

        size_words_bytes = int(size_words_bytes_str, 16)
        assert size_words_bytes % 4 == 0

        return size_words_bytes // 4

    @staticmethod
    def _get_base(module: _UDict, memory_type: str) -> int:
        base = module.get("base_addrs")
        assert isinstance(base, dict)

        base_addr_rom = base.get(memory_type)
        assert isinstance(base_addr_rom, dict)

        base_addr = base_addr_rom.get("hart")
        assert isinstance(base_addr, str)

        return int(base_addr, 16)

    @staticmethod
    def from_hjson_path(path: str, mode: str) -> "Scrambler":
        mc_params = mem_ctrl_params(mode)

        with open(path) as handle:
            top = hjson.load(handle, use_decimal=True)

        assert isinstance(top, dict)
        modules = top.get('module')
        assert isinstance(modules, list)

        mem_ctrl = Scrambler._get_mem_ctrl(modules,
                                           mc_params.module_type,
                                           mc_params.ctrl_name)
        size_words = Scrambler._get_size_words(mem_ctrl, mc_params.memory_type)
        base = Scrambler._get_base(mem_ctrl, mc_params.memory_type)
        params = Scrambler._get_params(mem_ctrl)
        nonce = Scrambler._get_param_value(params,
                                           mc_params.nonce,
                                           mc_params.nonce_width)
        key = Scrambler._get_param_value(params,
                                         mc_params.scr_key,
                                         mc_params.scr_key_width)

        return Scrambler(nonce, key, base, size_words)

    def flatten(self, mem: MemFile) -> MemFile:
        '''Flatten and pad mem up to the correct size

        This adds 8 trailing zero words as space to store the expected hash.
        These are (obviously!) not the right hash: we inject them properly
        later.

        '''
        digest_size_words = 8
        initial_len = self.rom_size_words - digest_size_words

        flattened = mem.flatten(initial_len)
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
        full_keystream = int(
            prince(to_scramble, self.key, self.num_rounds_half))

        return full_keystream & ((1 << width) - 1)

    def addr_sp_enc(self, log_addr: int) -> int:
        assert self._addr_width < 64
        data_nonce_width = 64 - self._addr_width
        addr_scr_nonce = self.nonce >> data_nonce_width
        return subst_perm_enc(log_addr, addr_scr_nonce, self._addr_width,
                              self.subst_perm_rounds)

    def addr_sp_dec(self, phy_addr: int) -> int:
        assert self._addr_width < 64

        data_nonce_width = 64 - self._addr_width
        addr_scr_nonce = self.nonce >> data_nonce_width
        return subst_perm_dec(phy_addr, addr_scr_nonce, self._addr_width,
                              self.subst_perm_rounds)

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
        to_hash = bytearray()
        for log_addr in range(self.rom_size_words - num_digest_words):
            phy_addr = self.addr_sp_enc(log_addr)
            scr_word = scr_chunk.words[phy_addr]
            # Note that a scrambled word with ECC amounts to 39bit. The
            # expression (39 + 7) // 8 calculates the amount of bytes that are
            # required to store these bits.
            to_hash.extend(scr_word.to_bytes((39 + 7) // 8, byteorder='little'))

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
                exp39 = ecc_encode_some(self.config, 'inv_hsiao', 32,
                                        [clr32])[0][0]
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
    parser.add_argument('mode')
    parser.add_argument('infile', type=argparse.FileType('rb'))
    parser.add_argument('outfile', type=argparse.FileType('w'))

    args = parser.parse_args()
    scrambler = Scrambler.from_hjson_path(args.hjson, args.mode)

    # Load the input ELF file
    clr_mem = MemFile.load_elf32(args.infile, scrambler.rom_base)

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
    collision = scr_mem.first_collision()
    if collision:
        addr0, addr1 = collision
        print(
            'ERROR: This combination of ROM contents and scrambling\n'
            '       key results in one or more collisions where\n'
            '       different addresses have the same data.\n'
            '\n'
            '       Looks like we\'ve been (very) unlucky with the\n'
            '       birthday problem. As a work-around, try again after\n'
            '       generating some different RndCnst* parameters.\n',
            '\n'
            f'First colliding addresses: {addr0:#010x}, {addr1:#010x}',
            file=sys.stderr)
        return 1

    scr_mem.write_vmem(args.outfile)
    return 0


if __name__ == '__main__':
    sys.exit(main())
