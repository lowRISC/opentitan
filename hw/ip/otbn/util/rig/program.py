# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Dict, List, Optional, TextIO, Tuple

from shared.insn_yaml import Insn, InsnsFile


class ProgInsn:
    '''An object representing a single instruction in the generated program

    self.insn is the instruction (as defined in insns.yml).

    self.operands has the encoded value for each operand (see the documentation
    for OperandType for more information).

    self.lsu_info is non-None if (and only if) the instruction is an LSU
    instruction. In this case, it's a pair (mem_type, addr). mem_type is the
    memory type (a key for Model._known_mem). addr is the target address of the
    LSU instruction (it's much easier to store it explicitly than to grovel
    around in the model to figure it out again from register values)

    '''
    def __init__(self,
                 insn: Insn,
                 operands: List[int],
                 lsu_info: Optional[Tuple[str, int]]):
        assert len(insn.operands) == len(operands)
        assert (lsu_info is None) is (insn.lsu is None)
        assert insn.syntax is not None

        self.insn = insn
        self.operands = operands
        self.lsu_info = lsu_info

    def to_asm(self, cur_pc: int) -> str:
        '''Return an assembly representation of the instruction'''
        # Build a dictionary from operand name to value from self.operands,
        # which is a list of operand values in the same order as insn.operands.
        op_vals = {}
        assert len(self.insn.operands) == len(self.operands)
        for operand, enc_val in zip(self.insn.operands, self.operands):
            op_val = operand.op_type.enc_val_to_op_val(enc_val, cur_pc)
            assert op_val is not None
            op_vals[operand.name] = op_val

        return self.insn.disassemble(cur_pc, op_vals)

    def to_json(self) -> object:
        '''Serialize to an object that can be written as JSON'''
        return (self.insn.mnemonic, self.operands, self.lsu_info)

    @staticmethod
    def from_json(insns_file: InsnsFile,
                  where: str,
                  json: object) -> 'ProgInsn':
        '''The inverse of to_json.

        where is a textual description of where we are in the file, used in
        error messages.

        '''
        if not (isinstance(json, list) and len(json) == 3):
            raise ValueError('{}, top-level data is not a triple.'
                             .format(where))

        mnemonic, operands, json_lsu_info = json

        if not isinstance(mnemonic, str):
            raise ValueError('{}, mnemonic is {!r}, not a string.'
                             .format(where, mnemonic))

        if not isinstance(operands, list):
            raise ValueError('{}, operands are not represented by a list.'
                             .format(where))
        op_vals = []
        for op_idx, operand in enumerate(operands):
            if not isinstance(operand, int):
                raise ValueError('{}, operand {} is not an integer.'
                                 .format(where, op_idx))
            if operand < 0:
                raise ValueError('{}, operand {} is {}, '
                                 'but should be non-negative.'
                                 .format(where, op_idx, operand))
            op_vals.append(operand)

        lsu_info = None
        if json_lsu_info is not None:
            if not (isinstance(json_lsu_info, list) and
                    len(json_lsu_info) == 2):
                raise ValueError('{}, non-None LSU info is not a pair.'
                                 .format(where))
            mem_type, addr = json_lsu_info

            if not isinstance(mem_type, str):
                raise ValueError('{}, LSU info mem_type is not a string.'
                                 .format(where))
            # These are the memory types in Model._known_regs, but we can't
            # import that without a circular dependency. Rather than being
            # clever, we'll just duplicate them for now.
            if mem_type not in ['dmem', 'csr', 'wsr']:
                raise ValueError('{}, invalid LSU mem_type: {!r}.'
                                 .format(where, mem_type))

            if not isinstance(addr, int):
                raise ValueError('{}, LSU info target addr is not an integer.'
                                 .format(where))
            if addr < 0:
                raise ValueError('{}, LSU info target addr is {}, '
                                 'but should be non-negative.'
                                 .format(where, addr))

            lsu_info = (mem_type, addr)

        insn = insns_file.mnemonic_to_insn.get(mnemonic)
        if insn is None:
            raise ValueError('{}, unknown instruction {!r}.'
                             .format(where, mnemonic))

        if (lsu_info is None) is not (insn.lsu is None):
            raise ValueError('{}, LSU info is {}given, but the {} instruction '
                             '{} it.'
                             .format(where,
                                     'not ' if lsu_info is None else '',
                                     mnemonic,
                                     ("doesn't expect"
                                      if insn.lsu is None else "expects")))
        if len(insn.operands) != len(op_vals):
            raise ValueError('{}, {} instruction has {} operands, but {} '
                             'seen in JSON data.'
                             .format(where, mnemonic,
                                     len(insn.operands), len(op_vals)))
        if insn.syntax is None:
            raise ValueError('{}, {} instruction has no syntax defined.'
                             .format(where, mnemonic))

        return ProgInsn(insn, op_vals, lsu_info)


class Program:
    '''An object representing the random program that is being generated.

    '''
    # The data for a section we're currently adding to. The tuples are
    # (sec_vma, space_left, insns) where sec_vma is the address of the start of
    # the section, space_left is the number of instructions that can be added
    # to the section before we run out of space and insns is a list of
    # instructions for the section.
    _SecData = Tuple[int, int, List[ProgInsn]]

    def __init__(self,
                 imem_lma: int, imem_size: int,
                 dmem_lma: int, dmem_size: int) -> None:
        assert imem_size & 3 == 0
        self.imem_lma = imem_lma
        self.imem_size = imem_size
        self.dmem_lma = dmem_lma
        self.dmem_size = dmem_size

        # A map from base address (VMA) to a list of instructions. Each
        # instruction is 4 bytes long, so a "section" of N instructions has
        # size 4N bytes.
        self._sections = {}  # type: Dict[int, List[ProgInsn]]

        # The number of instructions' space available. If we aren't below any
        # branches, this is the space available in imem. When we're branching,
        # this might be less.
        self.space = self.imem_size // 4

    def copy(self) -> 'Program':
        '''Return a a shallow copy of the program

        This is a shallow copy, so shares ProgInsn instances, but it can be
        modified by adding instructions without affecting the original.

        '''
        ret = Program(self.imem_lma, self.imem_size,
                      self.dmem_lma, self.dmem_size)
        ret._sections = {base: section.copy()
                         for base, section in self._sections.items()}
        ret.space = self.space
        return ret

    def add_insns(self, addr: int, insns: List[ProgInsn]) -> None:
        '''Add a sequence of instructions, starting at addr'''
        assert addr & 3 == 0
        assert addr <= self.imem_size

        assert len(insns) <= self.space
        self.space -= len(insns)

        sec_top = addr + 4 * len(insns)

        # This linear search is a bit naff, but I doubt it will have a
        # significant performance impact.
        next_above = self.imem_size
        sec_above = None
        prev_sec_base = None  # type: Optional[int]
        for section_base, section_insns in self._sections.items():
            if addr <= section_base:
                if section_base < next_above:
                    next_above = section_base
                    sec_above = section_insns
            else:
                if prev_sec_base is None or prev_sec_base < section_base:
                    prev_sec_base = section_base

        # At this point, next_above is the base of the first section
        # immediately after addr (or the top of memory if there isn't one).
        # prev_sec_base is None if addr is below all existing sections or is
        # the address of the highest section that starts below addr.
        assert addr < next_above

        # If next_above < sec_top, we've not got space to fit the instructions
        # we're trying to add. The caller's not supposed to do that, so fail an
        # assertion.
        assert sec_top <= next_above

        if prev_sec_base is not None:
            # If there is a previous section, check there is no overlap.
            prev_sec = self._sections[prev_sec_base]
            prev_sec_top = prev_sec_base + 4 * len(prev_sec)
            assert prev_sec_top <= addr

            # If prev_sec_top *equals* addr, we must merge the sections to
            # avoid generating two adjacent sections.
            if prev_sec_top == addr:
                if sec_above is not None and sec_top == next_above:
                    # We exactly bridge the gap between the two sections. In
                    # which case, add to the lower section and remove the upper
                    # one.
                    prev_sec += insns + sec_above
                    del self._sections[next_above]
                else:
                    # There's space (or the top of memory) above us. Add insns
                    # to the lower section.
                    prev_sec += insns
                return

        # Either there are no sections below addr or there is a gap between
        # addr and the previous section.
        if sec_above is not None and sec_top == next_above:
            # We're inserting instructions just below an existing section. Add
            # a new section consisting of insns and then the old section and
            # delete the latter.
            self._sections[addr] = insns + sec_above
            del self._sections[next_above]
        else:
            # The new section isn't touching anything else. Insert it, proud
            # and free! We explicitly take a copy of insns here so that we can
            # update entries in self._sections without modifying our input
            # argument.
            self._sections[addr] = list(insns)

    @staticmethod
    def _get_section_comment(idx: int,
                             addr: int,
                             insns: List[ProgInsn]) -> str:
        return ('/* Text section {} ([{:#06x}..{:#06x}]) */'
                .format(idx, addr, addr + 4 * len(insns) - 1))

    def dump_asm(self, out_file: TextIO, dsegs: Dict[int, List[int]]) -> None:
        '''Write an assembly representation of the program to out_file'''
        # Close any existing section, so that we can iterate over all the
        # instructions by iterating over self._sections.
        for idx, (addr, insns) in enumerate(sorted(self._sections.items())):
            comment = Program._get_section_comment(idx, addr, insns)
            out_file.write('{}{}\n'.format('\n' if idx else '', comment))
            out_file.write('.section .text.sec{:04}\n'.format(idx))
            for insn_off, pi in enumerate(insns):
                cur_pc = addr + 4 * insn_off
                out_file.write(pi.to_asm(cur_pc) + '\n')

        # Generate data .words
        for idx, (addr, values) in enumerate(sorted(dsegs.items())):
            out_file.write('\n/* Data section {} ({:#06x}-{:#06x}) */\n'
                           .format(idx, addr, addr + 4 * len(values) - 1))
            out_file.write('.section .data.sec{:04}\n'.format(idx))
            for value in values:
                out_file.write('.word {:#x}\n'.format(value))

    def dump_linker_script(self,
                           out_file: TextIO,
                           dsegs: Dict[int, List[int]]) -> None:
        '''Write a linker script to link the program

        This lays out the sections generated in dump_asm().

        '''
        seg_descs = []
        for idx, (addr, values) in enumerate(sorted(dsegs.items())):
            seg_descs.append(('dseg{:04}'.format(idx),
                              addr,
                              addr + self.dmem_lma,
                              '.data.sec{:04}'.format(idx),
                              ('/* Data section {} ({:#06x}-{:#06x}) */'
                               .format(idx, addr, addr + 4 * len(values) - 1))))
        for idx, (addr, insns) in enumerate(sorted(self._sections.items())):
            seg_descs.append(('iseg{:04}'.format(idx),
                              addr,
                              addr + self.imem_lma,
                              '.text.sec{:04}'.format(idx),
                              Program._get_section_comment(idx, addr, insns)))

        out_file.write('PHDRS\n'
                       '{\n')
        for seg, vma, lma, sec, comment in seg_descs:
            out_file.write('    {} PT_LOAD AT ( {:#x} );\n'.format(seg, lma))
        out_file.write('}\n\n')

        out_file.write('SECTIONS\n'
                       '{\n')
        for idx, (seg, vma, lma, sec, comment) in enumerate(seg_descs):
            out_file.write('{}    {}\n'.format('\n' if idx else '', comment))
            out_file.write('    {} {:#x} : AT({:#x})\n'
                           '    {{\n'
                           '        *({})\n'
                           '    }} : {}\n'
                           .format(sec, vma, lma, sec, seg))
        out_file.write('}\n')

    def pick_branch_targets(self,
                            cur_pc: int,
                            min_len: int,
                            count: int,
                            tgt_min: Optional[int],
                            tgt_max: Optional[int]) -> Optional[List[int]]:
        '''Pick count random targets for a branch destination

        As well as avoiding addresses that have program data, this also treats
        behaves as if there is an instruction at cur_pc (this is the
        instruction that's being picked).

        There is guaranteed to be at least space for min_len instructions at
        each target, but the weighting tries to favour places with some space
        for instruction sequences.

        If tgt_min is not None, the address returned will be at least tgt_min.
        Similarly for tgt_max.

        If we can't find space for the desired branch targets, returns None.

        '''

        # Round tgt_min and tgt_max inwards to multiples of 4 (because
        # instructions always have to be word aligned)
        if tgt_min is not None:
            tgt_min = (tgt_min + 3) & ~3
        if tgt_max is not None:
            tgt_max = tgt_max & ~3

        # To pick the targets, we start by choosing a "gap" between existing
        # sections in which they should land. To do *that*, we start by making
        # a list of all the gaps between sections in ascending order of base
        # address.
        section_list = [(base, len(insns))
                        for base, insns in self._sections.items()]
        section_list.append((cur_pc, 1))
        section_list.sort()

        gap_vma = 0
        gap_list = []
        for section_base, section_insns in section_list:
            assert gap_vma <= section_base

            # We only count the gap if it isn't completely below tgt_min and
            # isn't completely above tgt_max.
            if (((tgt_min is None or tgt_min < section_base) and
                 (tgt_max is None or gap_vma <= tgt_max))):
                # The minimum address we can pick is gap_vma, but we might need
                # to bump it up if tgt_min is specified.
                gap_lo = (max(gap_vma, tgt_min)
                          if tgt_min is not None else gap_vma)

                # The maximum address we can pick needs space for min_len
                # instructions before we get to section_base *and* must be at
                # most tgt_max if that is specified.
                gap_hi = section_base - 4 * min_len
                if tgt_max is not None:
                    gap_hi = min(gap_hi, tgt_max)

                # If we have anything to use, add it!
                if gap_lo <= gap_hi:
                    gap_list.append((gap_lo, gap_hi - gap_lo + 1))

            gap_vma = section_base + 4 * section_insns

        # Deal with any final gap above all known sections in the same way as
        # the internal gaps.
        gap_lo = (max(gap_vma, tgt_min)
                  if tgt_min is not None else gap_vma)
        gap_hi = self.imem_size - 4 * min_len
        if tgt_max is not None:
            gap_hi = min(gap_hi, tgt_max)
        if gap_lo <= gap_hi:
            gap_list.append((gap_lo, gap_hi - gap_lo + 1))

        ret = []
        for _ in range(count):

            # gap_list is an ordered list of pairs (addr, len), meaning "there
            # is a range of addresses that we can pick from, starting at
            # address addr and with length len bytes". If there are no gaps
            # left wide enough, gap_list will be empty and we should give up.
            if not gap_list:
                return None

            # Calculate weightings for the gaps. We weight by the extra length,
            # raised to some power (2.0, for now).
            gap_weight_pow = 2.0
            gap_weights = []
            for _, gap_len in gap_list:
                extra_len = gap_len - 4 * min_len
                gap_weights.append(1 + extra_len ** gap_weight_pow)

            idx = random.choices(range(len(gap_list)), weights=gap_weights)[0]

            # Now we have to decide what part of the gap to use. We choose the
            # offset in instructions from the start of the gap. Set
            # max_insn_off to the maximum allowed value (calculated as the
            # maximum byte offset, divided by the size of an instruction and
            # then minus the number of extra instructions that need to fit
            # afterwards).
            gap_vma, gap_len = gap_list[idx]
            max_insn_off = (gap_len - 1) // 4 - (min_len - 1)
            assert 0 <= max_insn_off

            # To try to avoid splitting gaps too much, we want to make it more
            # likely that we'll pick stuff "at the edges". Rather than doing
            # clever maths, we split the range into 3 parts:
            #
            #    | low |     middle      | high |
            #
            # where low and high are each 10% of the total range (leaving the
            # other 80% in middle).
            #
            # Pick 0 <= D <= 1 and assign the weight D/2 to each of low and
            # high and 1-D to the middle. Larger values of D mean we favour the
            # edges more.
            D = 0.5
            endpts = [(0, max_insn_off // 10),
                      (max_insn_off // 10, max_insn_off * 9 // 10),
                      (max_insn_off * 9 // 10, max_insn_off)]
            min_insn_off, max_insn_off = \
                random.choices(endpts, weights=[D / 2, 1 - D, D / 2])[0]

            assert min_insn_off <= max_insn_off

            # Now that we've picked a region, we choose an offset uniformly
            # from the range
            rng_len = max_insn_off - min_insn_off
            insn_off = (min_insn_off + int(0.5 + random.random() * rng_len))
            assert min_insn_off <= insn_off <= max_insn_off

            assert 4 * insn_off <= gap_len
            tgt = gap_vma + 4 * insn_off
            ret.append(tgt)

            # The last thing we need to do is update the gap list.
            new_gap_list = []
            for gap_lo, gap_len in gap_list:
                gap_top = gap_lo + gap_len

                # Does this gap give us a gap to the left of the range [tgt,
                # tgt + 4 * min_len]?
                left_top = min(gap_top, tgt - 4 * min_len)
                if gap_lo < left_top:
                    new_gap_list.append((gap_lo, left_top - gap_lo))

                # And how about to the right?
                right_lo = max(gap_lo, tgt + 4 * min_len)
                if right_lo < gap_top:
                    new_gap_list.append((right_lo, gap_top - right_lo))

            gap_list = new_gap_list

        assert len(ret) == count
        return ret

    def pick_branch_target(self,
                           cur_pc: int,
                           min_len: int,
                           tgt_min: Optional[int],
                           tgt_max: Optional[int]) -> Optional[int]:
        '''Pick a single random target for a branch destination

        A simple wrapper around the more general pick_branch_targets
        function.

        '''
        tgts = self.pick_branch_targets(cur_pc, min_len, 1, tgt_min, tgt_max)
        if tgts is None:
            return None

        assert len(tgts) == 1
        return tgts[0]

    def get_insn_space_at(self, addr: int) -> int:
        '''Return how many instructions there is space for, starting at addr

        Note that this doesn't take the global space constraint into
        account.

        '''
        space = self.imem_size - addr
        if space <= 0:
            return 0

        for sec_start, sec_insns in self._sections.items():
            sec_end = sec_start + 4 * len(sec_insns)
            if addr < sec_end:
                space = min(space, sec_start - addr)
                if space <= 0:
                    return 0

        return max(0, space // 4)
