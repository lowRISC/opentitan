# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import random
from typing import List, Tuple

from shared.insn_yaml import InsnsFile

from .program import Program
from .model import Model
from .snippet import Snippet
from .snippet_gen import SnippetGen

from .gens.ecall import ECall
from .gens.straight_line_insn import StraightLineInsn
from .gens.jump import Jump


class SnippetGens:
    '''A collection of snippet generators'''
    _WEIGHTED_CLASSES = [
        (ECall, 1.0),
        (StraightLineInsn, 1.0),
        (Jump, 0.1)
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
