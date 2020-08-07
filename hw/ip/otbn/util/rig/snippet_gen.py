# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import Insn, InsnsFile
from shared.lsu_desc import LSUDesc
from shared.operand import ImmOperandType, RegOperandType

from .program import ProgInsn, Program
from .model import Model
from .snippet import Snippet


class SnippetGen:
    '''A parameterised sequence of instructions

    These can be added to the instructions generated so far for a given random
    binary.

    '''
    def gen(self,
            size: int,
            model: Model,
            program: Program) -> Optional[Tuple[Snippet, bool, int]]:
        '''Try to generate instructions for this type of snippet.

        size is always positive and gives an upper bound on the number of
        instructions in the dynamic instruction stream that this should
        generate. For example, a loop of 10 instructions that goes around 10
        times would consume 100 from size.

        On success, inserts the instructions into program, updates the model,
        and returns a tuple (snippet, done, new_size). snippet is the generated
        snippet. done is true if the program is finished (if snippet ends with
        ecall) and is false otherwise. new_size is the size left after the
        generated snippet.

        On failure, leaves program and model unchanged and returns None. There
        should always be at least one snippet generator with positive weight
        (see pick_weight below) that succeeds unconditionally. This will be the
        ecall generator. Failure is interpreted as "this snippet won't work
        with the current program state", but the generator may be retried
        later.

        '''
        raise NotImplementedError('gen not implemented by subclass')

    def pick_weight(self,
                    size: int,
                    model: Model,
                    program: Program) -> float:
        '''Pick a weight by which to multiply this generator's default weight

        This is called for each generator before we start trying to generate a
        snippet for a given program and model state. This can be used to
        disable a generator when we know it won't work (if size is too small, for
        example).

        It can also be used to alter weights depending on where we are in the
        program. For example, a generator that generates ecall to end the
        program could decrease its weight when size is large, to avoid
        generating tiny programs by accident.

        The default implementation always returns 1.0.

        '''
        return 1.0


class ECall(SnippetGen):
    '''A generator that makes a snippet with a single ECALL instruction'''
    def __init__(self, insns_file: InsnsFile) -> None:
        ecall_insn = insns_file.mnemonic_to_insn.get('ecall')
        if ecall_insn is None:
            raise RuntimeError('No ECALL instruction in instructions file')

        if ecall_insn.operands:
            raise RuntimeError('ECALL instruction in instructions file '
                               'has a nonempty list of operands.')

        if ecall_insn.lsu:
            raise RuntimeError('ECALL instruction in instructions file '
                               'has unexpected LSU information.')

        self.insn = ProgInsn(ecall_insn, [], None)

    def gen(self,
            size: int,
            model: Model,
            program: Program) -> Optional[Tuple[Snippet, bool, int]]:
        snippet = Snippet([(model.pc, [self.insn])])
        snippet.insert_into_program(program)
        return (snippet, True, 0)

    def pick_weight(self,
                    size: int,
                    model: Model,
                    program: Program) -> float:
        # Choose small weights when size is large and large ones when it's
        # small.
        assert size > 0
        return (1e-10 if size > 5
                else 0.1 if size > 1
                else 1e10)


class StraightLineInsn(SnippetGen):
    '''A super-simple snippet consisting of a single instruction'''
    def __init__(self, insns_file: InsnsFile) -> None:
        # Find all the straight line, non-pseudo instructions in insns_file
        self.insns = []
        for insn in insns_file.insns:
            # Skip pseudo-ops
            if insn.python_pseudo_op or insn.literal_pseudo_op:
                continue

            # Skip anything that isn't straight-line
            if not insn.straight_line:
                continue

            # Skip bn.sid, bn.lid and bn.movr: These are indirect and we don't
            # currently track their sources properly (e.g. "bn.movr x2, x3"
            # reads from the WDR whose index is whatever is currently in x3)
            if insn.mnemonic in ['bn.sid', 'bn.lid', 'bn.movr']:
                continue

            self.insns.append(insn)

    def gen(self,
            size: int,
            model: Model,
            program: Program) -> Optional[Tuple[Snippet, bool, int]]:

        # Pick a (YAML) instruction at random. We'll probably do some clever
        # weighting here later on but, for now, we'll pick uniformly at the
        # start.
        weights = [1.0] * len(self.insns)

        prog_insn = None
        while prog_insn is None:
            idx = random.choices(range(len(self.insns)), weights=weights)[0]
            # Sanity check to make sure some weight was positive
            assert weights[idx] > 0

            # Try to fill out the instruction. On failure, clear the weight for
            # this index and go around again.
            prog_insn = self.fill_insn(self.insns[idx], model)
            if prog_insn is None:
                weights[idx] = 0
                continue

        # Success! We have generated an instruction. Put it in a snippet and
        # add that to the program
        snippet = Snippet([(model.pc, [prog_insn])])
        snippet.insert_into_program(program)

        # Then update the model with the instruction and update the model PC
        model.update_for_insn(prog_insn)
        model.pc += 4

        return (snippet, False, size - 1)

    def fill_insn(self, insn: Insn, model: Model) -> Optional[ProgInsn]:
        '''Try to fill out an instruction

        This might fail if, for example, the model doesn't have enough
        registers with architectural values. In that case, return None.

        '''

        # If this is not an LSU operation, or it is an LSU operation that
        # operates on CSR/WSRs, we can pick operands independently.
        if insn.lsu is None:
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

        # If this is an LSU operation, then the target address is given by the
        # sum of one or more operands. For each of these operands with a
        # register type, we are going to need to look in the model to figure
        # out the list of different known values we can give it. At the moment,
        # we only support the case when there is at most one non-register
        # operand, which must be an immediate. Grab that operand's name too.
        lsu_imm_op = None
        lsu_reg_ops = []
        lsu_reg_types = set()
        imm_op_min = 0
        imm_op_max = 0

        for tgt_op_name in insn.lsu.target:
            tgt_op = insn.name_to_operand[tgt_op_name]
            if isinstance(tgt_op.op_type, ImmOperandType):
                if lsu_imm_op is not None:
                    raise RuntimeError('Multiple immediate operands '
                                       'contribute to target for instruction '
                                       '{!r}. Not currently supported.'
                                       .format(insn.mnemonic))
                lsu_imm_op = tgt_op_name

                imm_op_range = tgt_op.op_type.get_range()
                if imm_op_range is None:
                    assert tgt_op.op_type.width is None
                    raise RuntimeError('The {!r} immediate operand for the '
                                       '{!r} instruction contributes to its '
                                       'LSU target but has no width.'
                                       .format(tgt_op_name, insn.mnemonic))

                imm_op_min, imm_op_max = imm_op_range
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
        lsu_type_to_info = {
            'mem-load': ('dmem', True),
            'mem-store': ('dmem', False),
            'csr': ('csr', True),
            'wsr': ('wsr', True)
        }
        assert set(lsu_type_to_info.keys()) == set(LSUDesc.TYPES)
        mem_type, loads_value = lsu_type_to_info[insn.lsu.lsu_type]

        tgt = model.pick_lsu_target(mem_type,
                                    loads_value,
                                    op_to_known_regs,
                                    imm_op_min,
                                    imm_op_max,
                                    insn.lsu.idx_width)
        if tgt is None:
            return None

        addr, imm_val, reg_indices = tgt
        assert imm_op_min <= imm_val <= imm_op_max

        op_vals = []
        for operand in insn.operands:
            # Is this the immediate? If the immediate operand is signed then
            # note that imm_op_min < 0 and we might have that imm_val < 0.
            # However, we store everything unsigned in op_vals, so we have to
            # reverse the 2s complement here.
            if operand.name == lsu_imm_op:
                assert isinstance(operand.op_type, ImmOperandType)
                op_vals.append(operand.op_type.encode_val(imm_val))
                continue

            # Or is it a register operand contributing to the target address?
            reg_val = reg_indices.get(operand.name)
            if reg_val is not None:
                op_vals.append(reg_val)
                continue

            # Otherwise it's some other operand. Pick any old value.
            val = model.pick_operand_value(operand.op_type)
            if val is None:
                return None
            op_vals.append(val)

        assert len(op_vals) == len(insn.operands)
        return ProgInsn(insn, op_vals, (mem_type, addr))


class SnippetGens:
    '''A collection of snippet generators'''
    _WEIGHTED_CLASSES = [
        (ECall, 1.0),
        (StraightLineInsn, 1.0)
    ]

    def __init__(self, insns_file: InsnsFile) -> None:
        self.generators = []  # type: List[Tuple[SnippetGen, float]]
        for cls, weight in SnippetGens._WEIGHTED_CLASSES:
            self.generators.append((cls(insns_file), weight))

    def gen(self,
            size: int,
            model: Model,
            program: Program) -> Tuple[Snippet, bool, int]:
        '''Pick a snippet and update model, program with its contents.

        Returns a pair (snippet, done, new_size) with the same meanings as
        Snippet.gen, except that new_size is clamped to be at least 1 if done
        is false. This avoids snippets having to special-case to make sure they
        aren't chosen when size is near zero. The end result might be a
        slightly longer instruction stream than we intended, but it shouldn't
        be much bigger.

        '''
        real_weights = []
        for generator, weight in self.generators:
            weight_mult = generator.pick_weight(size, model, program)
            real_weights.append(weight * weight_mult)

        while True:
            # Pick a generator based on the weights in real_weights.
            idx = random.choices(range(len(self.generators)),
                                 weights=real_weights)[0]
            generator, _ = self.generators[idx]

            # Note that there should always be at least one non-zero weight in
            # real_weights. random.choices doesn't check that: if you pass all
            # weights equal to zero, it always picks the last element. Since
            # that would cause an infinite loop, add a sanity check here to
            # make sure that the choice we made had positive weight.
            assert real_weights[idx] > 0

            # Run the generator to generate a snippet
            gen_res = generator.gen(size, model, program)
            if gen_res is not None:
                snippet, done, new_size = gen_res
                if not done:
                    new_size = max(new_size, 1)

                return (snippet, done, new_size)

            # If gen_res is None, the generator failed. Set that weight to zero
            # and try again.
            real_weights[idx] = 0.0
