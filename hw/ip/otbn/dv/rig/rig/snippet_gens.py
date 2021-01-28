# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Optional, Tuple

from shared.insn_yaml import InsnsFile

from .program import Program
from .model import Model
from .snippet import Snippet
from .snippet_gen import GenRet, SnippetGen

from .gens.branch import Branch
from .gens.ecall import ECall
from .gens.jump import Jump
from .gens.loop import Loop
from .gens.straight_line_insn import StraightLineInsn


class SnippetGens:
    '''A collection of snippet generators'''
    _WEIGHTED_CLASSES = [
        (Branch, 0.1),
        (ECall, 1.0),
        (Jump, 0.1),
        (Loop, 0.1),
        (StraightLineInsn, 1.0)
    ]

    def __init__(self, insns_file: InsnsFile) -> None:
        self.generators = []  # type: List[Tuple[SnippetGen, float]]
        for cls, weight in SnippetGens._WEIGHTED_CLASSES:
            self.generators.append((cls(insns_file), weight))

        # Grab an ECall generator. We'll use it in self.gens to append an ECALL
        # instruction if necessary.
        ecall = None
        for gen, _ in self.generators:
            if isinstance(gen, ECall):
                ecall = gen
                break
        assert ecall is not None
        assert isinstance(ecall, ECall)
        self.ecall = ecall

    def gen(self,
            model: Model,
            program: Program,
            ecall: bool) -> Optional[GenRet]:
        '''Pick a snippet and update model, program with its contents.

        This assumes that program.get_insn_space_at(model.pc) > 0.

        Normally returns a GenRet tuple with the same meanings as Snippet.gen.
        If the chosen snippet would generate an ECALL and ecall is False, this
        instead returns None (and leaves model and program unchanged).

        '''
        # If we've run out of fuel, stop immediately.
        if not model.fuel:
            return None

        real_weights = []
        pos_weights = 0
        for generator, weight in self.generators:
            if isinstance(generator, ECall) and not ecall:
                real_weight = 0.0
            else:
                weight_mult = generator.pick_weight(model, program)
                real_weight = weight * weight_mult

            assert real_weight >= 0
            if real_weight > 0:
                pos_weights += 1

            real_weights.append(real_weight)

        while pos_weights > 0:
            # Pick a generator based on the weights in real_weights.
            idx = random.choices(range(len(self.generators)),
                                 weights=real_weights)[0]
            generator, _ = self.generators[idx]

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
            pos_weights -= 1

        # We ran out of generators with positive weight. Give up.
        return None

    def _gen_ecall(self, pc: int, program: Program) -> Snippet:
        '''Generate an ECALL instruction at pc, ignoring notions of fuel'''
        assert program.get_insn_space_at(pc) > 0
        return self.ecall.gen_at(pc, program)

    def _gens(self,
              model: Model,
              program: Program,
              ecall: bool) -> Tuple[List[Snippet], Optional[Model]]:
        '''Generate some snippets to continue program.

        This will try to run down model.fuel and program.size. If ecall is
        True, it will eventually generate an ECALL instruction. If ecall is
        False then instead of generating the ECALL instruction, it will instead
        stop (leaving model.pc where the ECALL instruction would have been
        inserted).

        '''
        children = []  # type: List[Snippet]
        next_model = model  # type: Optional[Model]
        while True:
            assert next_model is not None

            must_stop = False
            # If we've run out of space and ecall is False, we stop
            # immediately. If ecall is True, we need to generate one last ECALL
            # instruction.
            if not program.space:
                if ecall:
                    must_stop = True
                else:
                    break

            old_fuel = next_model.fuel
            gen_res = None
            if not must_stop:
                gen_res = self.gen(next_model, program, ecall)

            if gen_res is None:
                # We failed to generate another snippet. If ecall is False,
                # that's fine: we've probably run out of fuel and should stop.
                # If ecall is True, that's bad news: we can't just leave the
                # program unfinished. In that case, force an ECALL instruction.
                if ecall:
                    children.append(self._gen_ecall(next_model.pc, program))
                    next_model = None
                break

            snippet, next_model = gen_res
            children.append(snippet)

            if next_model is None:
                assert ecall
                break

            assert next_model.fuel < old_fuel

        return (children, next_model)

    def gens(self,
             model: Model,
             program: Program) -> Tuple[Optional[Snippet], Model]:
        '''Try to generate snippets to continue program

        This will try to run down model.fuel and program.size. When it runs out
        of one or the other, it stops and returns any snippet it generated plus
        the updated model.

        '''
        snippets, next_model = self._gens(model, program, False)
        # _gens() only sets next_model to None if ecall is True.
        assert next_model is not None
        snippet = Snippet.merge_list(snippets) if snippets else None
        return (snippet, next_model)

    def gen_rest(self, model: Model, program: Program) -> Snippet:
        '''Generate the rest of the program, ending with an ECALL'''
        snippets, next_model = self._gens(model, program, True)
        # Since _gens() has finished with an ECALL, it always returns None for
        # next_model. It also always generates at least one snippet (containing
        # the ECALL).
        assert next_model is None
        assert snippets
        return Snippet.merge_list(snippets)
