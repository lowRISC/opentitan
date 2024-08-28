#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import subprocess
import tempfile
from typing import Any, BinaryIO, Dict, IO, List, Optional, TextIO, Tuple

from elftools.elf.elffile import ELFFile  # type: ignore
from util.design.secded_gen import ecc_encode_some, load_secded_config  # type: ignore


class MemChunk:
    def __init__(self, base_addr: int, words: List[int]):
        '''A contiguous list of words starting at base_addr'''
        self.base_addr = base_addr
        self.words = words

    def __str__(self) -> str:
        return ('MemChunk(@{:#x}, words_len={})'
                .format(self.base_addr, len(self.words)))

    def next_addr(self) -> int:
        '''Get the address directly above the chunk'''
        return self.base_addr + len(self.words)

    def write_vmem(self, width: int, outfile: TextIO) -> None:
        '''Write this chunk as one or more lines to outfile

        width is the maximum width of a word in bits.

        '''
        addr_chars = max(8, (self.next_addr().bit_length() + 3) // 4)
        word_chars = (width + 3) // 4

        # Try to wrap at 79 characters. To do this, pick a number of words so
        # that addr_chars + num_words * (word_chars + 1) fits (note that we
        # gain a character by adding a @ on the front of the address, but lose
        # it again by omitting the trailing space after the last word).
        nwords_on_line = max(1, (79 - addr_chars) // (1 + word_chars))
        for start_idx in range(0, len(self.words), nwords_on_line):
            line_addr = self.base_addr + start_idx
            toks = [f'@{line_addr:0{addr_chars}X}']
            for word in self.words[start_idx:start_idx + nwords_on_line]:
                toks.append(f'{word:0{word_chars}X}')
            outfile.write(' '.join(toks) + '\n')

    def add_ecc32(self, config: Dict[str, Any]) -> None:
        '''Add ECC32 integrity bits

        This extends the input words (which are assumed to be 32-bit) by 7
        bits, to make 39-bit words.

        '''
        self.words = ecc_encode_some(config, 'inv_hsiao', 32, self.words)[0]


class MemFile:
    def __init__(self, width: int, chunks: List[MemChunk]):
        self.width = width
        self.chunks = chunks
        self.config = load_secded_config()

    def __str__(self) -> str:
        return ('MemFile(width={}, chunks_len={})'
                .format(self.width, len(self.chunks)))

    @staticmethod
    def _parse_line(width: int, line: str) -> Tuple[int, List[int]]:
        '''Parse a line from a preprocessed vmem file

        Returns a pair (addr, words) where addr is the address at the start of
        the line and words is a list of the words that have been found, parsed
        to unsigned numbers. Assumes that line has at least one non-whitespace
        character. Each word is checked to make sure that it fits in width
        bits.

        '''
        tokens = line.split()
        assert tokens

        addr_match = re.match(r'@([0-9a-fA-F]+)$', tokens[0])
        if addr_match is None:
            raise ValueError('Bad line format: first token is {!r}, '
                             'which is not in the right format for an address.'
                             .format(tokens[0]))
        addr = int(addr_match.group(1), 16)

        words = []
        for idx, word_tok in enumerate(tokens[1:]):
            try:
                word = int(word_tok, 16)
            except ValueError:
                raise ValueError('Word {} of the line is invalid: '
                                 '{!r} is not a hex number.'
                                 .format(idx + 1, word_tok)) from None

            if word < 0 or word >> width:
                raise ValueError('Word {} of the line is {!r}, which '
                                 'does not fit in an unsigned {}-bit number.'
                                 .format(idx + 1, word_tok, width))
            words.append(word)

        return (addr, words)

    @staticmethod
    def _load_preproc(width: int, infile: IO[str]) -> 'MemFile':
        '''Load a pre-processed file'''
        chunks = []
        next_chunk = None  # type: Optional[MemChunk]
        for line in infile:
            # If the line is empty or whitespace, skip it.
            if not line or line.isspace():
                continue

            line_addr, line_words = MemFile._parse_line(width, line)

            # If there aren't actually any words on the line, skip it.
            if not line_words:
                continue

            if next_chunk is None:
                next_chunk = MemChunk(line_addr, line_words)
                continue

            # Glue the line onto the current chunk if there's no gap
            chunk_end = next_chunk.next_addr()
            if line_addr < chunk_end:
                raise ValueError("Cannot read data starting at {:#x}: "
                                 "we're already at {:#x}, so this would "
                                 "go backwards."
                                 .format(line_addr, chunk_end))
            if line_addr == chunk_end:
                next_chunk.words += line_words
                continue

            # If we're here, there's a gap between the current chunk and
            # line_addr.
            chunks.append(next_chunk)
            next_chunk = MemChunk(line_addr, line_words)

        if next_chunk is not None:
            chunks.append(next_chunk)

        return MemFile(width, chunks)

    @staticmethod
    def load_vmem(width: int, infile: TextIO) -> 'MemFile':
        '''Read a VMEM file

        This assumes that all words fit in the given width.

        '''
        with tempfile.TemporaryFile('w+') as tmp:
            # First, run cpp as a subprocess to strip out any comments. These
            # are allowed by the vmem format as described in srec_vmem(5) and
            # tokenising them is hard: get the C preprocessor to do the work
            # for us! The -P argument tells cpp not to generate linemarkers
            subprocess.run(['cpp', '-P'], stdin=infile, stdout=tmp, check=True)
            tmp.seek(0)
            return MemFile._load_preproc(width, tmp)

    @staticmethod
    def load_elf32(infile: BinaryIO, base_addr: int) -> 'MemFile':
        '''Read a little-endian 32-bit ELF file'''
        elf_file = ELFFile(infile)
        segments = []  # type: List[Tuple[int, int, bytes]]
        for segment in elf_file.iter_segments():
            seg_type = segment['p_type']

            # We're only interested in nonempty PT_LOAD segments
            if seg_type != 'PT_LOAD' or segment['p_filesz'] == 0:
                continue

            # seg_lma is the (relative) address of the first byte to be loaded.
            # seg_top is the address of the last byte to be loaded. A one-byte
            # segment will have seg_lma == seg_top.
            seg_lma = segment['p_paddr'] - base_addr
            seg_top = seg_lma + segment['p_filesz'] - 1

            assert seg_lma <= seg_top

            # We re-map the addresses relative to base_addr: check that no
            # segment starts before it.
            if seg_lma < 0:
                raise ValueError('ELF file contains a segment starting at '
                                 '{:#x}, so cannot be loaded relative to base '
                                 'address {:#x}.'
                                 .format(base_addr + seg_lma, base_addr))

            segments.append((seg_lma, seg_top, segment.data()))

        # Sort the segments by base address
        segments.sort(key=lambda t: t[0])

        # Make sure that they don't overlap
        prev_lma = 0
        next_addr = 0
        for lma, top, data in segments:
            if lma < next_addr:
                raise ValueError('ELF file contains overlapping segments with '
                                 'address ranges {:#x}..{:#x} and '
                                 '{:#x}..{:#x}.'
                                 .format(base_addr + prev_lma,
                                         base_addr + next_addr - 1,
                                         base_addr + lma,
                                         base_addr + top))
            prev_lma = lma
            next_addr = top + 1

        # Merge any adjacent segments, bridging any sub-word gaps. This doesn't
        # do any other right padding: we'll do that on the final pass that
        # converts to 32-bit words.
        merged_segments = []  # type: List[Tuple[int, int, bytes]]
        next_word = 0
        for lma, top, data in segments:
            # Round the LMA down to the previous word boundary. The non-overlap
            # check above should ensure that this is never actually less than
            # next_word.
            lma_word = lma // 4
            assert next_word <= lma_word

            # If there isn't an aligned whole word between the two segments,
            # bridge the gap
            if merged_segments and next_word == lma_word:
                last_lma_word, last_top, last_data = merged_segments[-1]
                if last_top < lma:
                    # The largest gap possible here happens with addresses like
                    # last_top = 0x100; lma = 0x107, which just bridges two
                    # 4-byte words (0x100..0x103 and 0x104..0x107) with one
                    # byte used from each, leaving 6 bytes to fill.
                    assert lma - (last_top + 1) <= 6
                    last_data += bytes(lma - (last_top + 1))
                merged_segments[-1] = (last_lma_word, top, last_data + data)
            else:
                # Pad on the left if necessary to ensure that lma is 32-bit
                # aligned.
                if lma % 4:
                    merged_segments.append((lma_word, top, bytes(lma % 4) + data))
                else:
                    merged_segments.append((lma_word, top, data))

            # The index of the first word that starts strictly above top.
            next_word = 1 + (top // 4)

        # Assemble the bytes in each segment into little-endian 32-bit words.
        # Zero-extend any partial word at the end of a segment. Because of the
        # merging in the previous pass, we know this won't cause any overlaps.
        chunks = []  # type: List[MemChunk]
        for lma_word, _, data in merged_segments:
            words = []
            word = 0
            for idx, byte in enumerate(data):
                shift = 8 * (idx % 4)
                word |= byte << shift
                if idx % 4 == 3:
                    words.append(word)
                    word = 0
            # idx here will be the index of the last byte. If data ended with a
            # partial word, idx will be something other than 3 mod 4.
            if idx % 4 != 3:
                words.append(word)

            chunks.append(MemChunk(lma_word, words))

        return MemFile(32, chunks)

    def next_addr(self) -> int:
        '''Get the address directly above the top of the MemFile'''
        return 0 if not self.chunks else self.chunks[-1].next_addr()

    def write_vmem(self, outfile: TextIO) -> None:
        '''Write data to a VMEM file'''
        for chunk in self.chunks:
            chunk.write_vmem(self.width, outfile)

    def flatten(self, size: int) -> 'MemFile':
        '''Flatten into a single chunk, padding with zeroes

        As well as padding between the chunks, this expands the result up to
        size words by adding padding after the last chunk if necessary.

        '''
        assert self.next_addr() <= size

        acc = MemChunk(0, [])
        # Add each chunk
        for chunk in self.chunks:
            acc_end = acc.next_addr()
            assert acc_end <= chunk.base_addr

            # If there's a gap before the chunk, pad it out with zeroes
            padding_len = chunk.base_addr - acc_end
            if padding_len:
                acc.words += [0 for _ in range(padding_len)]

            assert acc.next_addr() == chunk.base_addr
            acc.words += chunk.words

        acc_end = acc.next_addr()
        assert acc_end == self.next_addr()

        # If there's a gap after the last chunk, pad it out with zeroes
        padding_len = size - acc_end
        if padding_len:
            acc.words += [0 for _ in range(padding_len)]

        assert acc.next_addr() == size

        return MemFile(self.width, [acc])

    def add_ecc32(self) -> None:
        '''Add ECC32 integrity bits

        This extends the input words (which are assumed to be 32-bit) by 7
        bits, to make 39-bit words.

        '''
        assert self.width <= 32
        for chunk in self.chunks:
            chunk.add_ecc32(self.config)
        self.width = 39

    def first_collision(self) -> Optional[Tuple[int, int]]:
        '''Return the address of the first pair of colliding addresses

           If there is no such pair (which is hopefully the case), return None.
        '''
        known = {}  # type: Dict[int, int]
        for chunk in self.chunks:
            addr = chunk.base_addr
            for off, word in enumerate(chunk.words):
                if word in known:
                    return known[word], addr + off
                known[word] = addr + off
        return None
