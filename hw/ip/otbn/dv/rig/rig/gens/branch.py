# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import Optional, Sequence, Tuple

from shared.insn_yaml import InsnsFile
from shared.operand import ImmOperandType, RegOperandType

from .jump import Jump
from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import BranchSnippet, ProgSnippet, Snippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class Branch(SnippetGen):
    '''A generator that makes a snippet with a BEQ or BNE branch'''
    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        self.jump_gen = Jump(cfg, insns_file)
        self.beq = self._get_named_insn(insns_file, 'beq')
        self.bne = self._get_named_insn(insns_file, 'bne')

        # beq and bne expect operands: grs1, grs2, offset
        for insn in [self.beq, self.bne]:
            if not (len(insn.operands) == 3 and
                    isinstance(insn.operands[0].op_type, RegOperandType) and
                    insn.operands[0].op_type.reg_type == 'gpr' and
                    not insn.operands[0].op_type.is_dest() and
                    isinstance(insn.operands[1].op_type, RegOperandType) and
                    insn.operands[1].op_type.reg_type == 'gpr' and
                    not insn.operands[1].op_type.is_dest() and
                    isinstance(insn.operands[2].op_type, ImmOperandType) and
                    insn.operands[2].op_type.signed):
                raise RuntimeError('{} instruction from instructions file is not '
                                   'the shape expected by the Branch generator.'
                                   .format(insn.mnemonic))

        self.beq_prob = 0.5

        beq_weight = cfg.insn_weights.get('beq')
        bne_weight = cfg.insn_weights.get('bne')
        sum_weights = beq_weight + bne_weight
        if sum_weights == 0:
            self.disabled = True
        else:
            self.beq_prob = beq_weight / sum_weights

    _FloatRng = Tuple[float, float]
    _WeightedFloatRng = Tuple[float, _FloatRng]

    @staticmethod
    def pick_from_weighted_ranges(r: Sequence[_WeightedFloatRng]) -> float:
        ff0, ff1 = random.choices([rng for _, rng in r],
                                  weights=[w for w, _ in r])[0]
        return random.uniform(ff0, ff1)

    def _pick_tgt_addr(self,
                       pc: int,
                       off_min: int,
                       off_max: int,
                       program: Program) -> Optional[int]:
        '''Pick the target address for a branch'''
        # Make sure we can cover the case where we branch conditionally to
        # PC+4, which is probably quite unlikely otherwise, by giving at 1%
        # chance.
        #
        # We'll need at least 4 instructions' space for a proper branch: the
        # branch instruction, the fall-through instruction, the branch target
        # (which will jump back if necessary), and a continuation.
        if program.space < 4:
            fall_thru = True
        else:
            fall_thru = random.random() < 0.01

        return (pc + 4 if fall_thru else
                program.pick_branch_target(pc, 1, off_min, off_max))

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        # Return None if this is the last instruction in the current gap
        # because we need to either jump or do an ECALL to avoid getting stuck
        # (just like the StraightLineInsn generator)
        if program.get_insn_space_at(model.pc) <= 1:
            return None

        # Decide whether to generate BEQ or BNE.
        is_beq = random.random() < self.beq_prob

        insn = self.beq if is_beq else self.bne
        grs1_op, grs2_op, off_op = insn.operands

        assert isinstance(off_op.op_type, ImmOperandType)

        # Calculate the range of target addresses we can encode (this includes
        # any PC-relative adjustment)
        off_rng = off_op.op_type.get_op_val_range(model.pc)
        assert off_rng is not None
        off_min, off_max = off_rng

        # Pick the source GPRs that we're comparing.
        assert isinstance(grs1_op.op_type, RegOperandType)
        assert isinstance(grs2_op.op_type, RegOperandType)
        grs1 = model.pick_reg_operand_value(grs1_op.op_type)
        grs2 = model.pick_reg_operand_value(grs2_op.op_type)
        if grs1 is None or grs2 is None:
            return None

        tgt_addr = self._pick_tgt_addr(model.pc, off_min, off_max, program)
        if tgt_addr is None:
            return None

        assert off_min <= tgt_addr <= off_max

        off_enc = off_op.op_type.op_val_to_enc_val(tgt_addr, model.pc)
        assert off_enc is not None

        branch_insn = ProgInsn(insn, [grs1, grs2, off_enc], None)

        if tgt_addr == model.pc + 4:
            # If tgt_addr equals model.pc + 4, this actually behaves like a
            # straight-line instruction! Add the branch instruction, update the
            # model, and return.
            psnip = ProgSnippet(model.pc, [branch_insn])
            psnip.insert_into_program(program)
            model.update_for_insn(branch_insn)
            model.pc += 4
            return (psnip, model)

        # Decide how much of our remaining fuel to give the code below the
        # branch. Each side gets the same amount because only one side appears
        # in the instruction stream.
        fuel_frac_ranges = [(1, (0, 0.1)),
                            (10, (0.1, 0.5)),
                            (1, (0.5, 1.0))]
        fuel_frac = self.pick_from_weighted_ranges(fuel_frac_ranges)
        assert 0 <= fuel_frac <= 1
        assert 0 < model.fuel
        branch_fuel = max(1, int(0.5 + fuel_frac * model.fuel))

        # Similarly, decide how much of our remaining space to give the code
        # below the branch. Unlike with the fuel, we halve the result for each
        # side (since each side of the branch consumes instruction space)
        space_frac_ranges = fuel_frac_ranges
        space_frac = self.pick_from_weighted_ranges(space_frac_ranges)
        assert 0 <= space_frac <= 1
        # Subtract 2: one for the branch instruction and one for the start of
        # whatever happens after we re-merge. We checked earlier we had at
        # least 4 instructions' space left, so there should always be at least
        # 2 instructions' space left afterwards.
        #
        # Divide that by two (to apportion it between the branches) and then
        # subtract one more. This last subtraction is to allow the jump to
        # recombine.
        space_for_branches = program.space - 2
        assert space_for_branches >= 2
        total_branch_space = max(1, int(space_frac * (space_for_branches / 2)))
        assert 1 <= 2 * total_branch_space <= space_for_branches
        branch_space = total_branch_space - 1
        assert 0 <= branch_space

        # Make an updated copy of program that includes the branch instruction.
        # Similarly, take a copy of the model and update it as if we've fallen
        # through the branch instruction. Note that we can't just modify
        # program or model here because generation might fail.
        #
        # Insert a bogus instruction at tgt_addr into prog0. This represents
        # the first instruction on the other side of the branch: we need to do
        # this to avoid both sides of the branch trying to put an instruction
        # there.
        prog0 = program.copy()
        prog0.add_insns(model.pc, [branch_insn])
        model0 = model.copy()
        model0.update_for_insn(branch_insn)

        model0.pc += 4
        prog0.add_insns(tgt_addr, [branch_insn])

        # Pass branch_fuel - 1 here to give ourselves space for a jump to
        # branch 1 (if we decide to do it that way around)
        model0.fuel = branch_fuel - 1
        prog0.space = branch_space

        snippet0, model0 = cont(model0, prog0)
        # If snippet0 is None then we didn't manage to generate anything, but
        # that's fine. model0 will be unchanged and we just have an empty
        # sequence on the fall-through side of the branch.

        # Now generate the other side. Make another copy of program and insert
        # any instructions from snippet0 into it. Add the bogus instruction at
        # model.pc, as above. Also add a bogus instruction at model0.pc (if it
        # doesn't equal model.pc): this represents "the next thing" that
        # happens at the end of the first branch, and we mustn't allow snippet1
        # to use that space.
        prog1 = program.copy()
        prog1.add_insns(model.pc, [branch_insn])
        if snippet0 is None:
            assert model0.pc == model.pc + 4
        else:
            snippet0.insert_into_program(prog1)
            prog1.add_insns(model0.pc, [branch_insn])

        model1 = model.copy()
        model1.update_for_insn(branch_insn)
        model1.pc = tgt_addr

        prog1.space = branch_space
        model1.fuel = branch_fuel - 1

        snippet1, model1 = cont(model1, prog1)
        # If snippet1 is None, we didn't manage to generate anything here
        # either. As before, that's fine.

        # We've now generated both sides of the branch. All that's left to do
        # is fix up the execution paths to converge again. To do this, we need
        # to add a jump to one side or the other. (Alternatively, we could jump
        # from both to another address, but this shouldn't provide any extra
        # coverage, so there's not much point)
        if random.random() < 0.5:
            # Add the jump to go from branch 0 to branch 1.
            model0.fuel += 1
            prog0.space += 1
            jump_ret = self.jump_gen.gen_tgt(model0, prog0, model1.pc)
            if jump_ret is None:
                return None

            jmp_snippet, model0 = jump_ret
            snippet0 = Snippet.cons_option(snippet0, jmp_snippet)
        else:
            # Add the jump to go from branch 1 to branch 0
            model1.fuel += 1
            prog1.space += 1
            jump_ret = self.jump_gen.gen_tgt(model1, prog1, model0.pc)
            if jump_ret is None:
                return None

            jmp_snippet, model1 = jump_ret
            snippet1 = Snippet.cons_option(snippet1, jmp_snippet)

        assert model0.pc == model1.pc
        model0.merge(model1)

        snippet = BranchSnippet(model.pc, branch_insn, snippet0, snippet1)
        snippet.insert_into_program(program)
        return (snippet, model0)
