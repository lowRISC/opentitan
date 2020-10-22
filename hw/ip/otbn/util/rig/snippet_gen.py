# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''A module defining a base class for a snippet generator.

The generators in the ./gens/ subdirectory all derive from this class. To
actually generate some snippets, use the wrapper in snippet_gens.py.

'''

from typing import Optional, Tuple

from shared.insn_yaml import Insn, InsnsFile

from .program import Program
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

    def _get_named_insn(self, insns_file: InsnsFile, mnemonic: str) -> Insn:
        '''Get an instruction from insns_file by mnemonic

        This is used for specialized snippets that need to generate a specific
        instruction and wraps the error handling for when someone has removed
        the instruction from the file.

        '''
        insn = insns_file.mnemonic_to_insn.get(mnemonic.lower())
        if insn is None:
            raise RuntimeError('No {} instruction in instructions file.'
                               .format(mnemonic.upper()))
        return insn
