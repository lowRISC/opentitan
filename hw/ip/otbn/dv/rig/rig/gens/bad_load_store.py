# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.insn_yaml import Insn, InsnsFile

from ..config import Config
from ..model import Model
from ..program import ProgInsn, Program

from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class BadLoadStore(SnippetGen):
    '''A snippet generator that generates random lw/sw instructions

    Generated instructions are out of bounds, therefore end the
    program.

    '''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insns = []
        self.weights = []

        self.lw = self._get_named_insn(insns_file, 'lw')
        self.sw = self._get_named_insn(insns_file, 'sw')
        self.bnlid = self._get_named_insn(insns_file, 'bn.lid')
        self.bnsid = self._get_named_insn(insns_file, 'bn.sid')

        for insn in [self.sw, self.bnsid, self.lw, self.bnlid]:
            weight = cfg.insn_weights.get(insn.mnemonic)
            if weight > 0:
                self.weights.append(weight)
                self.insns.append(insn)

        # Check that at least one instruction has a positive weight
        assert len(self.insns) == len(self.weights)
        if not self.weights:
            self.disabled = True

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:

        weights = self.weights
        prog_insn = None
        while prog_insn is None:
            idx = random.choices(range(len(self.insns)), weights=weights)[0]
            # At least one weight should be positive. This is guaranteed so
            # long as fill_insn doesn't fail for absolutely everything. We know
            # that doesn't happen, because we have some instructions (such as
            # addi) where it will not fail.
            assert weights[idx] > 0

            # Try to fill out the instruction. On failure, clear the weight for
            # this index and go around again. We take the copy here, rather
            # than outside the loop, because we don't expect this to happen
            # very often.
            prog_insn = self.fill_insn(self.insns[idx], model)
            if prog_insn is None:
                weights = self.weights.copy()
                weights[idx] = 0
                continue

        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        return (snippet, model)

    def fill_insn(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Try to pick one of BN.XID or XW instructions

        '''

        # Special-case BN load/store instructions by mnemonic. These use
        # complicated indirect addressing, so it's probably more sensible to
        # give them special code.
        if insn.mnemonic in ['bn.lid', 'bn.sid']:
            return self._fill_bn_xid(insn, model)
        if insn.mnemonic in ['lw', 'sw']:
            return self._fill_xw(insn, model)

        return None

    def _fill_xw(self, insn: Insn, model: Model) -> Optional[ProgInsn]:

        grd_op_type = self.lw.operands[0].op_type
        imm_op_type = self.lw.operands[1].op_type

        # Determine the offset range for XW
        offset_rng = imm_op_type.get_op_val_range(model.pc)
        assert offset_rng is not None

        # Max/Min Offsets for XW (-2048, 2047)
        min_offset, max_offset = offset_rng

        # Get known registers
        known_regs = model.regs_with_known_vals('gpr')

        # We have two options for this generator: Barely OOB or OOB
        barely_oob = []
        oob = []

        for reg_idx, u_reg_val in known_regs:
            reg_val = u_reg_val - (1 << 32) if u_reg_val >> 31 else u_reg_val
            # We can reach to barely OOB by adding max_offset to smallest val
            # or adding min_offset (which is negative) to biggest possible val
            if reg_val - model.dmem_size in range(-max_offset, -min_offset):
                barely_oob.append((reg_idx, reg_val))
            # Negative OOB
            if reg_val + min_offset < 0:
                oob.append((reg_idx, reg_val))
            # Positive OOB
            if reg_val + max_offset > model.dmem_size:
                oob.append((reg_idx, reg_val))

        # Pick a representable target address that is (usually) correctly
        # aligned but doesn't lie in memory. If we can hit the "just out of
        # bounds" case, do so with high-ish probability.
        if random.random() < 0.2 and barely_oob:
            idx, val = random.choice(barely_oob)
            tgt_addr = model.dmem_size
        elif oob:
            # We're going for some arbitrary out-of-bounds address. First, pick
            # a register for the base address and then use it to calculate the
            # range of representable target addresses.
            idx, val = random.choice(oob)

            if val + min_offset <= -4:
                tgt_lo = val + min_offset
                tgt_hi = min(val + max_offset, -1)
            else:
                tgt_lo = max(model.dmem_size, val + min_offset)
                tgt_hi = val + max_offset

            # At this point, we can represent any value in [tgt_lo, tgt_hi],
            # but the addresses aren't necessarily aligned. Force correct
            # alignment (so that a misalignment check won't mask broken range
            # checks) most of the time.
            if random.random() < 0.9:
                # Round inwards and divide by 4. The result shouldn't be empty
                # because we know that tgt_lo <= -4 < tgt_hi (in the first
                # branch above) or, in the second branch, the only way that
                # tgt_lo could equal tgt_hi is if they are both
                # model.dmem_size, which is a multiple of 4.
                word_lo = (tgt_lo + 3) // 4
                word_hi = tgt_hi // 4
                assert word_lo <= word_hi

                word_addr = random.randint(word_lo, word_hi)
                tgt_addr = word_addr * 4
            else:
                tgt_addr = random.randint(tgt_lo, tgt_hi)
        else:
            return None

        imm_val = tgt_addr - val

        # Check if the final target address is in OOB region
        assert imm_val + val < 0 or imm_val + val >= model.dmem_size

        offset_val = imm_op_type.op_val_to_enc_val(imm_val, model.pc)
        assert offset_val is not None

        # Get the chosen base register index as grs1 operand.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        if insn.mnemonic == 'lw':
            # Pick grd randomly. Since we can write to any register
            # (including x0) this should always succeed.
            op_val_grd = model.pick_operand_value(grd_op_type)
            assert op_val_grd is not None

            op_val = [op_val_grd, offset_val, op_val_grs1]

        elif insn.mnemonic == 'sw':
            # Any known register is okay for grs2 operand since it will be
            # guaranteed to have an out of bounds address to store the value
            # from We definitely have a known register (x0), so this should
            # never fail
            op_val_grs2 = random.choice(known_regs)[0]

            op_val = [op_val_grs2, offset_val, op_val_grs1]

        return ProgInsn(insn, op_val, ('dmem', 4096))

    def _fill_bn_xid(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Fill out a BN.LID or BN.SID instruction'''

        bn_imm_op_type = self.bnlid.operands[2].op_type

        # Determine the offset range for BN.XID
        bn_offset_rng = bn_imm_op_type.get_op_val_range(model.pc)
        assert bn_offset_rng is not None

        # Max/Min Offsets for BN.XID (-512 * 32, 511 * 32)
        min_offset, max_offset = bn_offset_rng

        # Get known registers
        known_regs = model.regs_with_known_vals('gpr')

        idx, u_val = random.choice(known_regs)
        val = u_val - (1 << 32) if u_val >> 31 else u_val
        tgt_addr = random.randrange(val + min_offset, val + max_offset, 32)

        # Check if randomized tgt_addr is in OOB region.
        if tgt_addr >> 12:
            bn_imm_val = tgt_addr - val
        # If randomized tgt_addr is not in OOB region, make sure bn_imm_val is
        # big enough. So that the new resulting tgt_addr will definitely
        # be in OOB region.
        else:
            bn_imm_val = tgt_addr + model.dmem_size - val

        # Check if the final target address is in OOB region
        assert bn_imm_val + val < 0 or bn_imm_val + val >= model.dmem_size

        bn_offset_val = bn_imm_op_type.op_val_to_enc_val(bn_imm_val, model.pc)
        assert bn_offset_val is not None

        # Get the chosen base register index as grs1 operand.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        if insn.mnemonic == 'bn.lid':
            # Pick grd randomly. Since we can write to any register
            # (including x0) this should always succeed.
            op_val_grd = model.pick_operand_value(insn.operands[0].op_type)
            assert op_val_grd is not None

            op_val = [op_val_grd, op_val_grs1, bn_offset_val, 0, 0]

        elif insn.mnemonic == 'bn.sid':
            # Any known register is okay for grs2 operand since it will be
            # guaranteed to have an out of bounds address to store the value
            # from. We definitely have a known register (x0), so this should
            # never fail
            op_val_grs2 = random.choice(known_regs)[0]

            op_val = [op_val_grs1, op_val_grs2, bn_offset_val, 0, 0]

        return ProgInsn(insn, op_val, ('dmem', 4096))
