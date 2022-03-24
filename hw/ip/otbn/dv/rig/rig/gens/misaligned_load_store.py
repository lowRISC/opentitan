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


class MisalignedLoadStore(SnippetGen):
    '''A snippet generator that generates random load/store instructions

    Generated instructions are misaligned, therefore they end the
    program.

    '''

    ends_program = True

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insns = []
        self.weights = []

        self.sw = self._get_named_insn(insns_file, 'sw')
        self.lw = self._get_named_insn(insns_file, 'lw')

        # BN.LID Instruction Checks
        self.bnlid = self._get_named_insn(insns_file, 'bn.lid')

        # BN.SID Instruction Checks
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

            # If all 4 instructions are not successful, give up.
            if not weights[idx]:
                return None

            # Try to fill out the instruction. On failure, clear the weight for
            # this index and go around again.
            prog_insn = self.fill_insn(self.insns[idx], model)
            if prog_insn is None:
                weights[idx] = 0
                continue

        weights = self.weights.copy()
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

        base = []
        for reg_idx, reg_val in known_regs:
            val = reg_val - (1 << 32) if reg_val >> 31 else reg_val
            if 1 - max_offset <= val < model.dmem_size - min_offset:
                base.append((reg_idx, val))

        # We always have x0 as an eligible register for misaligned load/stores
        assert base

        # Pick a random register among known registers that is constrained
        # above
        idx, value = random.choice(base)

        op_val_grs1 = idx
        assert op_val_grs1 is not None

        imm_val = None
        for _ in range(50):
            # Pick a random offset value. We will change it later for
            # guaranteeing misaligned addresses.
            imm_val = random.randrange(min_offset, max_offset)
            addr = imm_val + value
            if (addr % 4) and (0 <= addr < model.dmem_size):
                break
        # The loop body above should succeed 75% of the time, so we should only
        # get here without an imm_val one time in 2^200.
        assert imm_val is not None

        offset_val = imm_op_type.op_val_to_enc_val(imm_val, model.pc)
        assert offset_val is not None

        if insn.mnemonic == 'lw':
            # Pick grd randomly. Since we can write to any register (including
            # x0) this should always succeed.
            op_val_grd = model.pick_operand_value(grd_op_type)
            assert op_val_grd is not None

            op_val = [op_val_grd, offset_val, op_val_grs1]

        elif insn.mnemonic == 'sw':
            # Any known register is okay for grs2 operand since it will be
            # guaranteed to have a misaligned address to store the value from.
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

        base = []

        # Get misaligned registers which can easily be in valid address range
        for reg_idx, reg_val in known_regs:
            val = reg_val - (1 << 32) if reg_val >> 31 else reg_val
            if (((1 - max_offset <= val < model.dmem_size - min_offset) and
                 val % 32)):
                base.append((reg_idx, val))

        if not base:
            return None

        # Pick a random register among known registers for initialization
        idx, value = random.choice(base)

        for _ in range(50):
            # Pick a random offset value. We will change it later for
            # guaranteeing valid misaligned addresses.
            bn_imm_val = random.randrange(min_offset, max_offset, 32)
            addr = bn_imm_val + value
            if (addr % 32) and (0 <= addr < model.dmem_size):
                break

        bn_offset_val = bn_imm_op_type.op_val_to_enc_val(bn_imm_val, model.pc)
        assert bn_offset_val is not None

        # Get the chosen base register index as grs1 operand.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        if insn.mnemonic == 'bn.lid':
            # Pick grd randomly. Since we can write to any register (including
            # x0) this should always succeed.
            op_val_grd = model.pick_operand_value(insn.operands[0].op_type)
            assert op_val_grd is not None

            op_val = [op_val_grd, op_val_grs1, bn_offset_val, 0, 0]

        elif insn.mnemonic == 'bn.sid':
            # Any known register is okay for grs2 operand since it will be
            # guaranteed to have an out of bounds address to store the value
            # from.
            op_val_grs2 = random.choice(known_regs)[0]
            assert op_val_grs2 is not None

            op_val = [op_val_grs1, op_val_grs2, bn_offset_val, 0, 0]

        return ProgInsn(insn, op_val, ('dmem', 4096))
