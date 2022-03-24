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


class EdgeLoadStore(SnippetGen):
    '''A snippet generator that generates random stores that try to
    hit edge cases.

    '''
    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.insns = []
        self.weights = []

        self.sw = self._get_named_insn(insns_file, 'sw')
        self.bnsid = self._get_named_insn(insns_file, 'bn.sid')

        for insn in [self.sw, self.bnsid]:
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

        # Return None if this is the last instruction in the current gap
        # because we need to either jump or do an ECALL to avoid getting stuck.
        if program.get_insn_space_at(model.pc) <= 1:
            return None

        weights = self.weights
        chosen_insn = random.choices(self.insns, weights=weights)[0]

        prog_insn = self.fill_insn(chosen_insn, model)
        if prog_insn is None:
            return None

        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)
        model.update_for_insn(prog_insn)
        model.pc += 4
        return (snippet, model)

    def fill_insn(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Try to pick one of BN.SID or SW instructions

        '''

        # Special-case BN store instruction by mnemonic. These use
        # complicated indirect addressing, so it's probably more sensible to
        # give them special code.
        if insn.mnemonic in ['bn.sid']:
            return self._fill_bn_sid(insn, model)
        if insn.mnemonic in ['sw']:
            return self._fill_sw(insn, model)

        return None

    def _fill_sw(self, insn: Insn, model: Model) -> Optional[ProgInsn]:

        imm_op_type = self.sw.operands[1].op_type

        # Determine the offset range for SW
        offset_rng = imm_op_type.get_op_val_range(model.pc)
        assert offset_rng is not None

        # Max/Min Offsets for SW (-2048, 2047)
        min_offset, max_offset = offset_rng

        # Get known registers
        known_regs = model.regs_with_known_vals('gpr')

        base = []

        for reg_idx, u_reg_val in known_regs:
            reg_val = u_reg_val - (1 << 32) if u_reg_val >> 31 else u_reg_val
            off_to_top = model.dmem_size - reg_val - 4
            if off_to_top in range(min_offset, max_offset + 1):
                base.append((reg_idx, reg_val))

        if not base:
            return None

        # Pick a random known register that can reach the top of memory
        idx, value = random.choice(base)

        imm_val = model.dmem_size - 4 - value

        addr = imm_val + value
        assert addr == model.dmem_size - 4

        offset_val = imm_op_type.op_val_to_enc_val(imm_val, model.pc)
        assert offset_val is not None

        # Get the chosen base register index as grs1 operand.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        # Any known register is okay for grs2 operand since it will be
        # guaranteed to have an out of bounds address to store the value from.
        # We definitely ave a known register (x0), so this should never fail
        op_val_grs2 = random.choice(known_regs[0])

        op_val = [op_val_grs2, offset_val, op_val_grs1]

        return ProgInsn(insn, op_val, ('dmem', addr))

    def _fill_bn_sid(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Fill out a BN.SID instruction'''

        bn_imm_op_type = self.bnsid.operands[2].op_type

        # Determine the offset range for BN.SID
        bn_offset_rng = bn_imm_op_type.get_op_val_range(model.pc)
        assert bn_offset_rng is not None

        # Max/Min Offsets for BN.SID (-512 * 32, 511 * 32)
        min_offset, max_offset = bn_offset_rng

        # Get known GPRs and the WDRs with an architecturally specified value
        known_regs = model.regs_with_known_vals('gpr')
        known_wdrs = set(model.regs_with_architectural_vals('wdr'))
        if not known_wdrs:
            return None

        base = []
        valid_grs2s = []

        # Choose not too big not too little register values
        # Also find a register for grs1 and grs2 operands
        for reg_idx, u_reg_val in known_regs:
            reg_val = u_reg_val - (1 << 32) if u_reg_val >> 31 else u_reg_val
            if ((model.dmem_size - reg_val - 32
                 in range(min_offset, max_offset + 1) and not reg_val % 32)):
                base.append((reg_idx, reg_val))
            if reg_val < 32 and reg_val in known_wdrs:
                valid_grs2s.append(reg_idx)

        if not valid_grs2s:
            return None

        if not base:
            return None

        # Pick a random register among known registers
        idx, value = random.choice(base)
        bn_imm_val = model.dmem_size - 32 - value
        addr = bn_imm_val + value
        assert addr == model.dmem_size - 32

        bn_offset_val = bn_imm_op_type.op_val_to_enc_val(bn_imm_val, model.pc)
        assert bn_offset_val is not None

        # Get the chosen base register index as grs1 operand.
        op_val_grs1 = idx
        assert op_val_grs1 is not None

        # Any known register is okay for grs2 operand since it will be
        # guaranteed to have an out of bounds address to store the value from.
        # We definitely have a known register (x0), so this should never fail
        op_val_grs2 = random.choice(valid_grs2s)

        op_val = [op_val_grs1, op_val_grs2, bn_offset_val, 0, 0]

        return ProgInsn(insn, op_val, ('dmem', addr))
