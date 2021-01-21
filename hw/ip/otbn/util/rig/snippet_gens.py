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
from .gens.straight_line_insn import StraightLineInsn


class SnippetGens:
    '''A collection of snippet generators'''
    _WEIGHTED_CLASSES = [
        (Branch, 0.1),
        (ECall, 1.0),
        (Jump, 0.1),
        (StraightLineInsn, 1.0)
    ]

    def __init__(self, insns_file: InsnsFile) -> None:
        self.generators = []  # type: List[Tuple[SnippetGen, float]]
        for cls, weight in SnippetGens._WEIGHTED_CLASSES:
            self.generators.append((cls(insns_file), weight))

    def gen(self,
            model: Model,
            program: Program,
            ecall: bool) -> Optional[GenRet]:
        '''Pick a snippet and update model, program with its contents.

        Normally returns a GenRet tuple with the same meanings as Snippet.gen.
        If the chosen snippet would generate an ECALL and ecall is False, this
        instead returns None (and leaves model and program unchanged).

        '''
        real_weights = []
        for generator, weight in self.generators:
            weight_mult = generator.pick_weight(model, program)
            real_weights.append(weight * weight_mult)

        # Define a continuation (which basically just calls self.gens()) to
        # pass to each generator. This allows recursive generation and avoids
        # needing circular imports to get the types right.
        def cont(md: Model, prg: Program) -> Optional[Tuple[Snippet, Model]]:
            ret = self.gens(md, prg, False)
            if ret is None:
                return None
            snippet, model = ret
            # We should always have a Model returned (because the ecall
            # argument was False)
            assert model is not None
            return (snippet, model)

        while True:
            # Pick a generator based on the weights in real_weights.
            idx = random.choices(range(len(self.generators)),
                                 weights=real_weights)[0]
            generator, _ = self.generators[idx]

            # Note that there should always be at least one non-zero weight in
            # real_weights. random.choices doesn't check that: if you pass all
            # weights equal to zero, it always picks the last element. Since
            # that would cause an infinite loop, add a check here to make sure
            # that the choice we made had positive weight.
            assert real_weights[idx] > 0

            if isinstance(generator, ECall) and not ecall:
                return None

            # Run the generator to generate a snippet
            gen_res = generator.gen(cont, model, program)
            if gen_res is not None:
                return gen_res

            # If gen_res is None, the generator failed. Set that weight to zero
            # and try again.
            real_weights[idx] = 0.0

    def gens(self,
             model: Model,
             program: Program,
             ecall: bool) -> Optional[GenRet]:
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
            old_fuel = next_model.fuel
            gr = self.gen(next_model, program, ecall)
            if gr is None:
                assert ecall is False
                break

            snippet, next_model = gr
            children.append(snippet)

            if next_model is None:
                break

            assert next_model.fuel < old_fuel

        if not children:
            assert ecall is False
            return None

        snippet = Snippet.merge_list(children)
        return (snippet, next_model)
