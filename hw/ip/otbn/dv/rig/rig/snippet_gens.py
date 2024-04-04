# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import InsnsFile

from .config import Config
from .program import Program
from .model import Model
from .snippet import Snippet
from .snippet_gen import GenRet, SnippetGen

from .gens.branch import Branch
from .gens.call_stack_rw import CallStackRW, BadCallStackRW
from .gens.ecall import ECall
from .gens.jump import Jump
from .gens.edge_load_store import EdgeLoadStore
from .gens.known_wdr import KnownWDR
from .gens.loop import Loop
from .gens.loop_dup_end import LoopDupEnd
from .gens.small_val import SmallVal
from .gens.straight_line_insn import StraightLineInsn

from .gens.bad_at_end import BadAtEnd
from .gens.bad_bnmovr import BadBNMovr
from .gens.bad_branch import BadBranch
from .gens.bad_deep_loop import BadDeepLoop
from .gens.bad_insn import BadInsn
from .gens.bad_giant_loop import BadGiantLoop
from .gens.bad_load_store import BadLoadStore
from .gens.bad_zero_loop import BadZeroLoop
from .gens.bad_ispr import BadIspr
from .gens.misaligned_load_store import MisalignedLoadStore
from .gens.untaken_branch import UntakenBranch


class SnippetGens:
    '''A collection of snippet generators'''
    _CLASSES = [
        Branch,
        CallStackRW,
        EdgeLoadStore,
        Jump,
        Loop,
        LoopDupEnd,
        SmallVal,
        StraightLineInsn,
        KnownWDR,
        UntakenBranch,

        ECall,
        BadAtEnd,
        BadBNMovr,
        BadBranch,
        BadCallStackRW,
        BadDeepLoop,
        BadInsn,
        BadGiantLoop,
        BadLoadStore,
        BadZeroLoop,
        BadIspr,
        MisalignedLoadStore
    ]

    def __init__(self, cfg: Config, insns_file: InsnsFile) -> None:
        self._cont_generators = []  # type: List[Tuple[SnippetGen, float]]
        self._end_generators = []   # type: List[Tuple[SnippetGen, float]]

        # Grab an ECall generator. We'll use it in self.gens to append an ECALL
        # instruction if necessary.
        ecall = None

        used_names = set()

        for cls in SnippetGens._CLASSES:
            cls_name = cls.__name__
            weight = cfg.gen_weights.values.get(cls_name)
            if weight is None:
                raise ValueError('No weight in config at {} '
                                 'for generator {!r}.'
                                 .format(cfg.path, cls_name))
            gen = cls(cfg, insns_file)
            if isinstance(gen, ECall):
                ecall = gen

                # The ECall generator mustn't disable itself
                assert not gen.disabled

                # It also shouldn't be disabled by a config
                if weight == 0:
                    raise ValueError(f'Config at {cfg.path} gives zero weight '
                                     f'to the ECall generator.')

            assert cls_name not in used_names
            used_names.add(cls_name)

            if weight > 0 and not gen.disabled:
                pr = (gen, weight)
                if cls.ends_program:
                    self._end_generators.append(pr)
                else:
                    self._cont_generators.append(pr)

        # self._end_generators should include ECall, at least.
        assert self._end_generators

        # Check that we used all the names in cfg.gen_weights
        unused_names = set(cfg.gen_weights.values.keys()) - used_names
        if unused_names:
            raise ValueError('Config at {} gives weights to non-existent '
                             'generators: {}.'
                             .format(cfg.path,
                                     ', '.join(sorted(unused_names))))

        assert ecall is not None
        assert isinstance(ecall, ECall)
        self.ecall = ecall

    def gen(self,
            model: Model,
            program: Program,
            end: bool) -> Optional[GenRet]:
        '''Pick a snippet and update model, program with its contents.

        This assumes that program.get_insn_space_at(model.pc) > 0.

        Normally returns a GenRet tuple with the same meanings as Snippet.gen.
        If the chosen snippet would cause execution to halt but end is False,
        this instead returns None (and leaves model and program unchanged).

        '''
        # If we've run out of fuel, stop immediately.
        if not model.fuel:
            return None

        generators = self._end_generators if end else self._cont_generators

        real_weights = []
        num_pos_weights = 0
        for generator, weight in generators:
            weight_mult = generator.pick_weight(model, program)
            real_weight = weight * weight_mult

            assert real_weight >= 0
            if real_weight > 0:
                num_pos_weights += 1

            real_weights.append(real_weight)

        while num_pos_weights > 0:
            # Pick a generator based on the weights in real_weights.
            idx = random.choices(range(len(generators)),
                                 weights=real_weights)[0]
            generator, _ = generators[idx]

            # Note that there should always be at least one positive weight in
            # real_weights. random.choices doesn't check that: if you pass all
            # weights equal to zero, it always picks the last element. Since
            # that would cause an infinite loop, add a check here to make sure
            # that the choice we made had positive weight.
            assert real_weights[idx] > 0

            # Run the generator to generate a snippet
            gen_res = generator.gen(self.gens, model, program)
            if gen_res is not None:
                return gen_res

            # If gen_res is None, the generator failed. Set that weight to zero
            # and try again.
            real_weights[idx] = 0.0
            num_pos_weights -= 1

        # We ran out of generators with positive weight. Give up.
        return None

    def _gen_ecall(self, pc: int, program: Program) -> Snippet:
        '''Generate an ECALL instruction at pc, ignoring notions of fuel'''
        assert program.get_insn_space_at(pc) > 0
        return self.ecall.gen_at(pc, program)

    def _gens(self,
              model: Model,
              program: Program,
              end: bool) -> Tuple[List[Snippet], Model]:
        '''Generate some snippets to continue program.

        This will try to run down model.fuel and program.size. If end is True,
        it will eventually generate an ECALL instruction or cause an error. If
        end is False then, instead of doing that, it will instead stop (leaving
        model.pc at the place where the next instruction should be inserted).

        '''
        children = []  # type: List[Snippet]
        while True:
            gen_ecall = False
            # If we've run out of space and end is False, we stop immediately.
            # If end is True, we need to bail out now! Generate one last ECALL
            # instruction.
            if not program.space:
                if end:
                    gen_ecall = True
                else:
                    break

            old_fuel = model.fuel
            gen_res = None
            if not gen_ecall:
                gen_res = self.gen(model, program, end)

            if gen_res is None:
                # We failed to generate another snippet. If end is False,
                # that's fine: we've probably run out of fuel and should stop.
                # If end is True, that's bad news: we can't just leave the
                # program unfinished. In that case, force an ECALL instruction.
                if end:
                    children.append(self._gen_ecall(model.pc, program))
                break

            snippet, model = gen_res
            children.append(snippet)

            if end:
                break

            assert model.fuel < old_fuel

        return (children, model)

    def gens(self,
             model: Model,
             program: Program,
             end: bool) -> Tuple[Optional[Snippet], Model]:
        '''Try to generate snippets to continue program

        This will try to run down model.fuel and program.size. When it runs out
        of one or the other, it stops and returns any snippet it generated plus
        the updated model. If end is true, the generated snippet should cause
        OTBN to stop.

        '''
        snippets, next_model = self._gens(model, program, end)
        # If end was True, there must be at least one instruction
        assert snippets or not end
        snippet = Snippet.merge_list(snippets) if snippets else None
        return (snippet, next_model)

    def gen_program(self,
                    model: Model,
                    program: Program) -> Tuple[Snippet, int]:
        '''Generate an entire program

        This is the top-level entry point used by gen_program in rig.py.

        '''
        # The basic strategy is that we split the length of program execution
        # (given by model.fuel) into a head and a tail. We generate the "head
        # part", trying not to generate an ECALL or error. Following that, we
        # generate the "tail part", explicitly aiming to end in an ECALL or
        # error.

        head_fuel_min = max(1, int(model.fuel * 0.9))
        head_fuel_max = model.fuel - 1
        head_fuel = random.randint(head_fuel_min, head_fuel_max)
        assert 1 <= head_fuel < model.fuel

        tail_fuel = model.fuel - head_fuel

        model.fuel = head_fuel
        head, model = self.gens(model, program, False)
        # Add the rest of the fuel to the tank
        model.fuel += tail_fuel

        tail_snippets, end_model = self._gens(model, program, True)
        # _gens() always generates at least one snippet (containing the final
        # ECALL or an instruction that causes an error). The model it returns
        # points at that final instruction's PC.
        assert tail_snippets

        snippets = tail_snippets if head is None else [head] + tail_snippets

        return (Snippet.merge_list(snippets), end_model.pc)
