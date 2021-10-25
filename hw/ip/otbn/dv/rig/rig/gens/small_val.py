# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional

from shared.operand import ImmOperandType, RegOperandType
from shared.insn_yaml import InsnsFile

from ..config import Config
from ..model import Model
from ..program import ProgInsn, Program
from ..snippet import ProgSnippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class SmallVal(SnippetGen):
    '''A snippet generator that generates writes small values to registers

    We do so using addi (which is modelled fully in model.py), which means we
    can then use those small values for later instructions: useful for things
    like loop counters.

    '''

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        if 'addi' not in insns_file.mnemonic_to_insn:
            raise RuntimeError('ADDI instruction not in instructions file')
        self.insn = insns_file.mnemonic_to_insn['addi']

        # ADDI has three operands: grd, grs1 and imm.
        if not (len(self.insn.operands) == 3 and
                isinstance(self.insn.operands[0].op_type, RegOperandType) and
                self.insn.operands[0].op_type.reg_type == 'gpr' and
                isinstance(self.insn.operands[1].op_type, RegOperandType) and
                self.insn.operands[1].op_type.reg_type == 'gpr' and
                isinstance(self.insn.operands[2].op_type, ImmOperandType) and
                self.insn.operands[2].op_type.signed):
            raise RuntimeError('ADDI instruction from instructions file is not '
                               'the shape expected by the SmallVal generator.')

        self.grd_op_type = self.insn.operands[0].op_type
        self.grs1_op_type = self.insn.operands[1].op_type
        self.imm_op_type = self.insn.operands[2].op_type

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # Return None if this is the last instruction in the current gap
        # because we need to either jump or do an ECALL to avoid getting stuck.
        if program.get_insn_space_at(model.pc) <= 1:
            return None

        # Pick grd any old way: we can write to any register. This should
        # always succeed.
        grd_val = model.pick_operand_value(self.grd_op_type)
        assert grd_val is not None

        # Pick a target value. As well as "genuinely small" values, we also
        # want to see some small-ish values that can be used as bases for
        # address calculations. These need to be 2-byte, 4-byte or 32-byte
        # aligned, for misaligned jumps, aligned jumps and correctly-aligned
        # BN.LID/BN.SID operations, respectively.
        shift = random.choices([0, 1, 2, 5], weights=[7, 1, 1, 1])[0]

        # Figure out the range of representable values (this is important for
        # larger shifts to make sure we don't try for something we can't
        # represent). This will always succeed (because addi isn't PC-relative
        # and model.pc isn't None anyway)
        rng = self.imm_op_type.get_op_val_range(model.pc)
        assert rng is not None

        # Shift rng down to get the range of representable "unshifted" values.
        # Round inwards.
        lo, hi = rng
        lo_sh = (lo + (1 << shift) // 2) >> shift
        hi_sh = hi >> shift
        assert lo_sh <= hi_sh

        # Truncate to [-10, 10] (which is what gives the "small" part)
        lb = max(lo_sh, -10)
        ub = min(hi_sh, 10)
        assert lb <= ub

        tgt_val = random.randint(lb, ub) << shift

        # We'll use x0 as the register source. Since the register source has
        # value zero, we need -tgt_val as our immediate. The small range of
        # possible target values should mean this is always representable.
        imm_encoded = self.imm_op_type.op_val_to_enc_val(-tgt_val, model.pc)
        assert imm_encoded is not None

        op_vals = [grd_val, 0, imm_encoded]

        prog_insn = ProgInsn(self.insn, op_vals, None)
        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        model.update_for_insn(prog_insn)
        model.pc += 4

        return (snippet, model)
