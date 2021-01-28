# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import Insn, InsnsFile
from shared.lsu_desc import LSUDesc
from shared.operand import ImmOperandType, OptionOperandType, RegOperandType

from ..config import Config
from ..program import ProgInsn, Program
from ..model import Model
from ..snippet import ProgSnippet, Snippet
from ..snippet_gen import GenCont, GenRet, SnippetGen


class StraightLineInsn(SnippetGen):
    '''A super-simple snippet consisting of a single instruction'''
    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        super().__init__()

        # Find all the straight line, non-pseudo instructions in insns_file
        self.insns = []
        self.weights = []

        seen_insns = set()
        for insn in insns_file.insns:
            # Skip pseudo-ops
            if insn.python_pseudo_op or insn.literal_pseudo_op:
                continue

            seen_insns.add(insn.mnemonic)

            # Skip anything that isn't straight-line
            if not insn.straight_line:
                continue

            weight = cfg.insn_weights.get(insn.mnemonic)
            if weight > 0:
                self.insns.append(insn)
                self.weights.append(weight)

        # Check that the config's insn-weights dictionary didn't have any
        # non-existent instructions. Note that we even add jumps to seen_insns:
        # although weighting those won't make any difference here, this is the
        # code that makes sense of what's allowed.
        missing_insns = set(cfg.insn_weights.values.keys()) - seen_insns
        if missing_insns:
            raise ValueError('Config at {} defines weights for '
                             'non-existent instructions: {}'
                             .format(cfg.path,
                                     ', '.join(sorted(missing_insns))))

        # Check that at least one instruction has a positive weight
        assert len(self.insns) == len(self.weights)
        if not self.insns:
            raise ValueError('Config at {} defines a zero weight '
                             'for all instructions.'
                             .format(cfg.path))

    def gen(self,
            cont: GenCont,
            model: Model,
            program: Program) -> Optional[GenRet]:
        return self._gen(model, program)

    def gen_some(self,
                 count: int,
                 model: Model,
                 program: Program) -> Optional[Tuple[Snippet, Model]]:
        '''Generate a block of count straight-line instructions'''
        assert 0 < count

        # Take a copy of model, so that we fail atomically
        model = model.copy()

        children = []  # type: List[Snippet]
        for i in range(count):
            gen_ret = self._gen(model, program)
            if gen_ret is None:
                return None

            snippet, model = gen_ret
            children.append(snippet)

        return (Snippet.merge_list(children), model)

    def _gen(self,
             model: Model,
             program: Program) -> Optional[Tuple[Snippet, Model]]:
        # Return None if this is the last instruction in the current gap
        # because we need to either jump or do an ECALL to avoid getting stuck.
        #
        # Note that we could do this by defining pick_weight, but we don't
        # expect it to happen very often so it's probably best (and cheaper)
        # just to disable ourselves on the rare occasions when it does.
        if program.get_insn_space_at(model.pc) <= 1:
            return None

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

        # Success! We have generated an instruction. Put it in a snippet and
        # add that to the program
        snippet = ProgSnippet(model.pc, [prog_insn])
        snippet.insert_into_program(program)

        # Then update the model with the instruction and update the model PC
        model.update_for_insn(prog_insn)
        model.pc += 4

        return (snippet, model)

    def fill_insn(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Try to fill out an instruction

        This might fail if, for example, the model doesn't have enough
        registers with architectural values. In that case, return None.

        Note that there are some instructions that will never return None. For
        example, addi, which can always expand to "addi x0, x0, 0" (also known
        as nop).

        '''

        # Special-case BN load/store instructions by mnemonic. These use
        # complicated indirect addressing, so it's probably more sensible to
        # give them special code.
        if insn.mnemonic in ['bn.lid', 'bn.sid']:
            return self._fill_bn_xid(insn, model)
        if insn.mnemonic == 'bn.movr':
            return self._fill_bn_movr(insn, model)

        # If this is not an LSU operation, or it is an LSU operation that
        # operates on CSR/WSRs, we can pick operands independently.
        if insn.lsu is None:
            return self._fill_non_lsu_insn(insn, model)

        return self._fill_lsu_insn(insn, model)

    def _fill_non_lsu_insn(self,
                           insn: Insn,
                           model: Model) -> Optional[ProgInsn]:
        '''Fill out an instruction with no LSU component'''
        assert insn.lsu is None
        # For each operand, pick a value that's allowed by the model (i.e.
        # one that won't trigger any undefined behaviour)
        op_vals = []
        for operand in insn.operands:
            op_val = model.pick_operand_value(operand.op_type)
            if op_val is None:
                return None

            op_vals.append(op_val)

        assert len(op_vals) == len(insn.operands)
        return ProgInsn(insn, op_vals, None)

    def _pick_gpr_with_arch_val(self, model: Model) -> int:
        '''Return the index of a GPR with an architectural value'''
        arch_gprs = model.regs_with_architectural_vals('gpr')
        # Since x0 always has a value, there will always be at least something
        assert arch_gprs
        return random.choices(arch_gprs)[0]

    def _pick_gpr_for_arch_wdr(self,
                               known_regs: List[Tuple[int, int]],
                               model: Model) -> Optional[int]:
        '''Return index of a GPR pointing to a WDR with architectural value'''
        arch_wdrs = set(model.regs_with_architectural_vals('wdr'))
        valid_gprs = []
        for gpr, gpr_val in known_regs:
            if gpr_val is None:
                continue
            wdr_idx = gpr_val & 31
            if wdr_idx in arch_wdrs:
                valid_gprs.append(gpr)

        if not valid_gprs:
            return None

        return random.choices(valid_gprs)[0]

    def _pick_inc_vals(self,
                       idx0: int,
                       idx1: int,
                       model: Model) -> Tuple[int, int]:
        '''Pick two values in 0, 1 that aren't both 1

        These are appropriate to use as the increment flags for
        BN.LID/BN.SID/BN.MOVR. idx0 and idx1 are the indices of the GPRs in
        question.

        '''
        options = [(0, 0), (1, 0), (0, 1)]
        wt10 = 0.0 if model.is_const('gpr', idx0) else 1.0
        wt01 = 0.0 if model.is_const('gpr', idx1) else 1.0
        return random.choices(options, weights=[1.0, wt10, wt01])[0]

    def _fill_bn_xid(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Fill out a BN.LID or BN.SID instruction'''
        if insn.mnemonic == 'bn.lid':
            is_load = True
            # bn.lid expects the operands: grd, grs1, offset, grs1_inc, grd_inc
            if len(insn.operands) != 5:
                raise RuntimeError('Unexpected number of operands for bn.lid')

            grd, grs1, offset, grs1_inc, grd_inc = insn.operands
            exp_shape = (
                # grd
                isinstance(grd.op_type, RegOperandType) and
                grd.op_type.reg_type == 'gpr' and
                not grd.op_type.is_dest() and
                # grs1
                isinstance(grs1.op_type, RegOperandType) and
                grs1.op_type.reg_type == 'gpr' and
                not grs1.op_type.is_dest() and
                # offset
                isinstance(offset.op_type, ImmOperandType) and
                offset.op_type.signed and
                # grs1_inc
                isinstance(grs1_inc.op_type, OptionOperandType) and
                # grd_inc
                isinstance(grd_inc.op_type, OptionOperandType)
            )
        else:
            assert insn.mnemonic == 'bn.sid'
            is_load = False
            # bn.sid expects the operands: grs1, grs2, offset, grs1_inc,
            # grs2_inc
            if len(insn.operands) != 5:
                raise RuntimeError('Unexpected number of operands for bn.sid')

            grs1, grs2, offset, grs1_inc, grs2_inc = insn.operands
            exp_shape = (
                # grs1
                isinstance(grs1.op_type, RegOperandType) and
                grs1.op_type.reg_type == 'gpr' and
                not grs1.op_type.is_dest() and
                # grs2
                isinstance(grs2.op_type, RegOperandType) and
                grs2.op_type.reg_type == 'gpr' and
                not grs2.op_type.is_dest() and
                # offset
                isinstance(offset.op_type, ImmOperandType) and
                offset.op_type.signed and
                # grs1_inc
                isinstance(grs1_inc.op_type, OptionOperandType) and
                # grs2_inc
                isinstance(grs2_inc.op_type, OptionOperandType)
            )

        if not exp_shape:
            raise RuntimeError('Unexpected shape for {}'.format(insn.mnemonic))

        # Assertions to guide mypy
        assert isinstance(offset.op_type, ImmOperandType)

        known_regs = model.regs_with_known_vals('gpr')
        if is_load:
            # bn.lid reads the bottom 5 bits of grd to get the index of the
            # destination WDR. We can pick any GPR that has an architectural
            # value.
            wdr_gpr_idx = self._pick_gpr_with_arch_val(model)
        else:
            # bn.sid looks at the bottom 5 bits of grs2 to get a source WDR.
            # Unlike bn.lid above, we need an architectural value in the
            # corresponding WDR. Thus we have to pick a GPR with a known value
            # which, in turn, points at a WDR with an architectural value.
            grs2_idx = self._pick_gpr_for_arch_wdr(known_regs, model)
            if grs2_idx is None:
                return None

            wdr_gpr_idx = grs2_idx

        # Now pick the source register and offset. The range for offset
        # shouldn't be none (because we know the width of the underlying bit
        # field).
        offset_rng = offset.op_type.get_op_val_range(model.pc)
        assert offset_rng is not None

        op_to_known_regs = {'grs1': known_regs}
        tgt = model.pick_lsu_target('dmem',
                                    is_load,
                                    op_to_known_regs,
                                    offset_rng,
                                    offset.op_type.shift,
                                    32)
        if tgt is None:
            return None

        addr, imm_val, reg_indices = tgt
        assert offset_rng[0] <= imm_val <= offset_rng[1]

        assert list(reg_indices.keys()) == ['grs1']
        grs1_idx = reg_indices['grs1']

        offset_val = offset.op_type.op_val_to_enc_val(imm_val, model.pc)
        assert offset_val is not None

        # Do we increment the GPRs? We can increment up to one of them.
        grs1_inc_val, wdr_gpr_inc_val = \
            self._pick_inc_vals(grs1_idx, wdr_gpr_idx, model)

        # Finally, package up the operands properly for the instruction we're
        # building.
        if is_load:
            # bn.lid: grd, grs1, offset, grs1_inc, grd_inc
            enc_vals = [wdr_gpr_idx, grs1_idx, offset_val,
                        grs1_inc_val, wdr_gpr_inc_val]
        else:
            # bn.sid: grs1, grs2, offset, grs1_inc, grs2_inc
            enc_vals = [grs1_idx, wdr_gpr_idx, offset_val,
                        grs1_inc_val, wdr_gpr_inc_val]

        return ProgInsn(insn, enc_vals, ('dmem', addr))

    def _fill_bn_movr(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Fill out a BN.MOVR instruction'''
        # bn.lid expects the operands: grd, grs, grd_inc, grs_inc
        if len(insn.operands) != 4:
            raise RuntimeError('Unexpected number of operands for bn.movr')

        grd, grs, grd_inc, grs_inc = insn.operands
        exp_shape = (
            # grd
            isinstance(grd.op_type, RegOperandType) and
            grd.op_type.reg_type == 'gpr' and
            not grd.op_type.is_dest() and
            # grs
            isinstance(grs.op_type, RegOperandType) and
            grs.op_type.reg_type == 'gpr' and
            not grs.op_type.is_dest() and
            # grd_inc
            isinstance(grd_inc.op_type, OptionOperandType) and
            # grs_inc
            isinstance(grs_inc.op_type, OptionOperandType)
        )
        if not exp_shape:
            raise RuntimeError('Unexpected shape for bn.movr')

        # For grs, we need to pick a GPR that points at a WDR with an
        # architectural value (since it will be the source of the move).
        known_regs = model.regs_with_known_vals('gpr')
        grs_idx = self._pick_gpr_for_arch_wdr(known_regs, model)
        if grs_idx is None:
            return None

        # For grd, we can pick any GPR with an architectural value (since it
        # defines the destination WDR)
        grd_idx = self._pick_gpr_with_arch_val(model)

        grd_inc_val, grs_inc_val = self._pick_inc_vals(grd_idx, grs_idx, model)

        return ProgInsn(insn,
                        [grd_idx, grs_idx, grd_inc_val, grs_inc_val],
                        None)

    def _fill_lsu_insn(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Fill out a generic load/store instruction'''
        # If this is an LSU operation, then the target address is given by the
        # sum of one or more operands. For each of these operands with a
        # register type, we are going to need to look in the model to figure
        # out the list of different known values we can give it. At the moment,
        # we only support the case when there is at most one non-register
        # operand, which must be an immediate. Grab that operand's name too.
        lsu_imm_op = None
        lsu_reg_ops = []
        lsu_reg_types = set()
        imm_op_range = (0, 0)
        imm_op_shift = 0

        assert insn.lsu is not None
        for tgt_op_name in insn.lsu.target:
            tgt_op = insn.name_to_operand[tgt_op_name]
            if isinstance(tgt_op.op_type, ImmOperandType):
                if lsu_imm_op is not None:
                    raise RuntimeError('Multiple immediate operands '
                                       'contribute to target for instruction '
                                       '{!r}. Not currently supported.'
                                       .format(insn.mnemonic))
                lsu_imm_op = tgt_op_name

                rng = tgt_op.op_type.get_op_val_range(model.pc)
                if rng is None:
                    assert tgt_op.op_type.width is None
                    raise RuntimeError('The {!r} immediate operand for the '
                                       '{!r} instruction contributes to its '
                                       'LSU target but has no width.'
                                       .format(tgt_op_name, insn.mnemonic))
                imm_op_range = rng
                imm_op_shift = tgt_op.op_type.shift
                continue

            if isinstance(tgt_op.op_type, RegOperandType):
                reg_type = tgt_op.op_type.reg_type
                lsu_reg_ops.append((tgt_op_name, reg_type))
                lsu_reg_types.add(reg_type)
                continue

            raise RuntimeError('Unknown operand type for {!r} operand of '
                               '{!r} instruction: {}.'
                               .format(tgt_op_name, insn.mnemonic,
                                       type(tgt_op.op_type).__name__))

        # We have a list of register operands, together with their types. Get a
        # list of registers with known values for each register type we've seen.
        known_regs_by_type = {rtype: model.regs_with_known_vals(rtype)
                              for rtype in lsu_reg_types}

        # And turn that into a dict keyed by operand name
        op_to_known_regs = {op_name: known_regs_by_type[op_type]
                            for op_name, op_type in lsu_reg_ops}

        # Ask the model to try to find a target we can use. If this is a load
        # or a CSR operation, it will have to be an address that already has an
        # architectural value. If a store, it can be any address in range.
        #
        # We cheat a bit for WSR stores. These don't actually load a value, but
        # we still want to make sure we pick a valid WSR index, so we claim we
        # loaded one anyway.
        lsu_type_to_info = {
            'mem-load': ('dmem', True),
            'mem-store': ('dmem', False),
            'csr': ('csr', True),
            'wsr-load': ('wsr', True),
            'wsr-store': ('wsr', True)
        }
        assert set(lsu_type_to_info.keys()) == set(LSUDesc.TYPES)
        mem_type, loads_value = lsu_type_to_info[insn.lsu.lsu_type]

        tgt = model.pick_lsu_target(mem_type,
                                    loads_value,
                                    op_to_known_regs,
                                    imm_op_range,
                                    imm_op_shift,
                                    insn.lsu.idx_width)
        if tgt is None:
            return None

        addr, imm_val, reg_indices = tgt
        assert imm_op_range[0] <= imm_val <= imm_op_range[1]

        enc_vals = []
        for operand in insn.operands:
            # Is this the immediate? If the immediate operand is signed then
            # note that imm_op_min < 0 and we might have that imm_val < 0.
            # However, we store everything as an enc_val, so we have to
            # "re-encode" here.
            if operand.name == lsu_imm_op:
                enc_val = operand.op_type.op_val_to_enc_val(imm_val, model.pc)
                assert enc_val is not None
                enc_vals.append(enc_val)
                continue

            # Or is it a register operand contributing to the target address?
            reg_val = reg_indices.get(operand.name)
            if reg_val is not None:
                enc_vals.append(reg_val)
                continue

            # Otherwise it's some other operand. Pick any old value.
            val = model.pick_operand_value(operand.op_type)
            if val is None:
                return None
            enc_vals.append(val)

        assert len(enc_vals) == len(insn.operands)
        return ProgInsn(insn, enc_vals, (mem_type, addr))
