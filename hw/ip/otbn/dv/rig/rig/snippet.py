# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional

from shared.insn_yaml import InsnsFile
from shared.mem_layout import get_memory_layout

from .program import ProgInsn, Program


class Snippet:
    '''A collection of instructions, generated as part of a random program.'''
    def insert_into_program(self, program: Program) -> None:
        '''Insert this snippet into the given program

        This assumes the parts of the snippet are disjoint from the existing
        instructions in the program.

        '''
        raise NotImplementedError()

    def to_json(self) -> object:
        '''Serialize to an object that can be written as JSON'''
        raise NotImplementedError()

    @staticmethod
    def _addr_from_json(where: str, json: object) -> int:
        '''Read an instruction address from a parsed json object'''

        # The address should be an aligned non-negative integer and insns
        # should itself be a list (of serialized Insn objects).
        if not isinstance(json, int):
            raise ValueError('First coordinate of {} is not an integer.'
                             .format(where))
        if json < 0:
            raise ValueError('Address of {} is {}, but should be non-negative.'
                             .format(where, json))
        if json & 3:
            raise ValueError('Address of {} is {}, '
                             'but should be 4-byte aligned.'
                             .format(where, json))
        return json

    @staticmethod
    def _from_json_lst(insns_file: InsnsFile,
                       idx: List[int],
                       json: List[object]) -> 'Snippet':
        raise NotImplementedError()

    @staticmethod
    def from_json(insns_file: InsnsFile,
                  idx: List[int],
                  json: object) -> 'Snippet':
        '''The inverse of to_json'''
        if not (isinstance(json, list) and json):
            raise ValueError('Snippet {} is not a nonempty list.'.format(idx))

        key = json[0]
        if not isinstance(key, str):
            raise ValueError('Key for snippet {} is not a string.'.format(idx))

        if key == 'BS':
            return BranchSnippet._from_json_lst(insns_file, idx, json[1:])
        if key == 'LS':
            return LoopSnippet._from_json_lst(insns_file, idx, json[1:])
        elif key == 'PS':
            return ProgSnippet._from_json_lst(insns_file, idx, json[1:])
        elif key == 'SS':
            return SeqSnippet._from_json_lst(insns_file, idx, json[1:])
        else:
            raise ValueError('Snippet {} has unknown key {!r}.'
                             .format(idx, key))

    def _merge(self, snippet: 'Snippet') -> bool:
        '''Merge snippet after this one and return True if possible.

        If not possible, leaves self unchanged and returns False.

        '''
        return False

    def merge(self, snippet: 'Snippet') -> 'Snippet':
        '''Merge snippet after this one

        On a successful merge, this will alter and return self. If a merge
        isn't possible, this generates and returns a SeqSnippet.

        '''
        if self._merge(snippet):
            return self

        return SeqSnippet([self, snippet])

    @staticmethod
    def merge_list(snippets: List['Snippet']) -> 'Snippet':
        '''Merge a non-empty list of snippets as much as possible'''
        assert snippets
        acc = []
        cur = snippets[0]
        for snippet in snippets[1:]:
            if cur._merge(snippet):
                continue

            acc.append(cur)
            cur = snippet

        acc.append(cur)
        return SeqSnippet(acc)

    @staticmethod
    def cons_option(snippet0: Optional['Snippet'],
                    snippet1: 'Snippet') -> 'Snippet':
        '''Cons together one or two snippets'''
        return snippet1 if snippet0 is None else snippet0.merge(snippet1)

    def to_program(self) -> Program:
        '''Write a series of disjoint snippets to make a program'''
        # Find the size of the memory that we can access. Both memories start
        # at address 0: a strict Harvard architecture. (mems[x][0] is the LMA
        # for memory x, not the VMA)
        mems = get_memory_layout()
        imem_lma, imem_size = mems['IMEM']
        dmem_lma, dmem_size = mems['DMEM']
        program = Program(imem_lma, imem_size, dmem_lma, dmem_size)
        self.insert_into_program(program)
        return program


class ProgSnippet(Snippet):
    '''A sequence of instructions that are executed in order'''
    def __init__(self, addr: int, insns: List[ProgInsn]):
        assert addr >= 0
        assert addr & 3 == 0

        self.addr = addr
        self.insns = insns

    def insert_into_program(self, program: Program) -> None:
        program.add_insns(self.addr, self.insns)

    def to_json(self) -> object:
        '''Serialize to an object that can be written as JSON'''
        return ['PS', self.addr, [i.to_json() for i in self.insns]]

    @staticmethod
    def _from_json_lst(insns_file: InsnsFile,
                       idx: List[int],
                       json: List[object]) -> Snippet:
        '''The inverse of to_json.'''
        # Each element should be a pair: (addr, insns).
        if len(json) != 2:
            raise ValueError('Snippet {} has {} arguments; '
                             'expected 2 for a ProgSnippet.'
                             .format(idx, len(json)))
        j_addr, j_insns = json

        where = 'snippet {}'.format(idx)
        addr = Snippet._addr_from_json(where, j_addr)

        if not isinstance(j_insns, list):
            raise ValueError('Second coordinate of {} is not a list.'
                             .format(where))

        insns = []
        for insn_idx, insn_json in enumerate(j_insns):
            pi_where = ('In snippet {}, instruction {}'
                        .format(idx, insn_idx))
            pi = ProgInsn.from_json(insns_file, pi_where, insn_json)
            insns.append(pi)

        return ProgSnippet(addr, insns)

    def _merge(self, snippet: Snippet) -> bool:
        if not isinstance(snippet, ProgSnippet):
            return False

        next_addr = self.addr + 4 * len(self.insns)
        if snippet.addr != next_addr:
            return False

        self.insns += snippet.insns
        return True


class SeqSnippet(Snippet):
    '''A nonempty sequence of snippets that run one after another'''
    def __init__(self, children: List[Snippet]):
        assert children
        self.children = children

    def insert_into_program(self, program: Program) -> None:
        for child in self.children:
            child.insert_into_program(program)

    def to_json(self) -> object:
        ret = ['SS']  # type: List[object]
        ret += [c.to_json() for c in self.children]
        return ret

    @staticmethod
    def _from_json_lst(insns_file: InsnsFile,
                       idx: List[int],
                       json: List[object]) -> Snippet:
        if len(json) == 0:
            raise ValueError('List at {} for SeqSnippet is empty.'.format(idx))

        children = []
        for i, item in enumerate(json):
            children.append(Snippet.from_json(insns_file, idx + [i], item))
        return SeqSnippet(children)


class BranchSnippet(Snippet):
    '''A snippet representing a branch

    branch_insn is the first instruction that runs, at address addr, then
    either snippet0 or snippet1 will run. The program will complete in either
    case.

    '''
    def __init__(self,
                 addr: int,
                 branch_insn: ProgInsn,
                 snippet0: Optional[Snippet],
                 snippet1: Optional[Snippet]):
        assert snippet0 is not None or snippet1 is not None
        self.addr = addr
        self.branch_insn = branch_insn
        self.snippet0 = snippet0
        self.snippet1 = snippet1

    def insert_into_program(self, program: Program) -> None:
        program.add_insns(self.addr, [self.branch_insn])
        if self.snippet0 is not None:
            self.snippet0.insert_into_program(program)
        if self.snippet1 is not None:
            self.snippet1.insert_into_program(program)

    def to_json(self) -> object:
        js0 = None if self.snippet0 is None else self.snippet0.to_json()
        js1 = None if self.snippet1 is None else self.snippet1.to_json()
        return ['BS',
                self.addr,
                self.branch_insn.to_json(),
                js0,
                js1]

    @staticmethod
    def _from_json_lst(insns_file: InsnsFile,
                       idx: List[int],
                       json: List[object]) -> Snippet:
        if len(json) != 4:
            raise ValueError('List for snippet {} is of the wrong '
                             'length for a BranchSnippet ({}, not 4)'
                             .format(idx, len(json)))

        j_addr, j_branch_insn, j_snippet0, j_snippet1 = json

        addr_where = 'address for snippet {}'.format(idx)
        addr = Snippet._addr_from_json(addr_where, j_addr)

        bi_where = 'branch instruction for snippet {}'.format(idx)
        branch_insn = ProgInsn.from_json(insns_file, bi_where, j_branch_insn)

        snippet0 = (None if j_snippet0 is None
                    else Snippet.from_json(insns_file, idx + [0], j_snippet0))
        snippet1 = (None if j_snippet1 is None
                    else Snippet.from_json(insns_file, idx + [1], j_snippet1))

        if snippet0 is None and snippet1 is None:
            raise ValueError('Both sides of branch snippet {} are None.'
                             .format(idx))

        return BranchSnippet(addr, branch_insn, snippet0, snippet1)


class LoopSnippet(Snippet):
    '''A snippet representing a loop'''
    def __init__(self, addr: int, hd_insn: ProgInsn, body: Snippet):
        self.addr = addr
        self.hd_insn = hd_insn
        self.body = body

    def insert_into_program(self, program: Program) -> None:
        program.add_insns(self.addr, [self.hd_insn])
        self.body.insert_into_program(program)

    def to_json(self) -> object:
        return ['LS',
                self.addr,
                self.hd_insn.to_json(),
                self.body.to_json()]

    @staticmethod
    def _from_json_lst(insns_file: InsnsFile,
                       idx: List[int],
                       json: List[object]) -> Snippet:
        if len(json) != 3:
            raise ValueError('List for snippet {} is of the wrong '
                             'length for a LoopSnippet ({}, not 4)'
                             .format(idx, len(json)))

        j_addr, j_hd_insn, j_body = json

        addr_where = 'address for snippet {}'.format(idx)
        addr = Snippet._addr_from_json(addr_where, j_addr)

        hi_where = 'head instruction for snippet {}'.format(idx)
        hd_insn = ProgInsn.from_json(insns_file, hi_where, j_hd_insn)
        body = Snippet.from_json(insns_file, idx + [0], j_body)

        return LoopSnippet(addr, hd_insn, body)
