# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Support code for reading the instruction database in insns.yml'''

import itertools
import re
from typing import Dict, List, Optional, Tuple, cast

import yaml

from .encoding import Encoding
from .encoding_scheme import EncSchemes
from .operand import Operand
from .syntax import InsnSyntax
from .yaml_parse_helpers import (check_keys, check_str, check_bool,
                                 check_list, index_list, get_optional_str)


class InsnGroup:
    def __init__(self, yml: object) -> None:
        yd = check_keys(yml, 'insn-group', ['key', 'title', 'doc'], [])
        self.key = check_str(yd['key'], 'insn-group key')
        self.title = check_str(yd['title'], 'insn-group title')
        self.doc = check_str(yd['doc'], 'insn-group doc')


class InsnGroups:
    def __init__(self, yml: object) -> None:
        self.groups = [InsnGroup(y) for y in check_list(yml, 'insn-groups')]
        if not self.groups:
            raise ValueError('Empty list of instruction groups: '
                             'we need at least one as a base group.')
        self.key_to_group = index_list('insn-groups',
                                       self.groups, lambda ig: ig.key)

    def default_group(self) -> str:
        '''Get the name of the default instruction group'''
        assert self.groups
        return self.groups[0].key


class Insn:
    def __init__(self,
                 yml: object,
                 groups: InsnGroups,
                 encoding_schemes: EncSchemes) -> None:
        yd = check_keys(yml, 'instruction',
                        ['mnemonic', 'operands'],
                        ['group', 'rv32i', 'synopsis',
                         'syntax', 'doc', 'note', 'trailing-doc',
                         'decode', 'operation', 'encoding', 'glued-ops',
                         'literal-pseudo-op', 'python-pseudo-op'])

        self.mnemonic = check_str(yd['mnemonic'], 'mnemonic for instruction')

        what = 'instruction with mnemonic {!r}'.format(self.mnemonic)
        self.operands = [Operand(y, self.mnemonic)
                         for y in check_list(yd['operands'],
                                             'operands for ' + what)]
        self.name_to_operand = index_list('operands for ' + what,
                                          self.operands,
                                          lambda op: op.name)

        raw_group = get_optional_str(yd, 'group', what)
        self.group = groups.default_group() if raw_group is None else raw_group

        if self.group not in groups.key_to_group:
            raise ValueError('Unknown instruction group, {!r}, '
                             'for mnemonic {!r}.'
                             .format(self.group, self.mnemonic))

        self.rv32i = check_bool(yd.get('rv32i', False),
                                'rv32i flag for ' + what)
        self.glued_ops = check_bool(yd.get('glued-ops', False),
                                    'glued-ops flag for ' + what)
        self.synopsis = get_optional_str(yd, 'synopsis', what)
        self.doc = get_optional_str(yd, 'doc', what)
        self.note = get_optional_str(yd, 'note', what)
        self.trailing_doc = get_optional_str(yd, 'trailing-doc', what)
        self.decode = get_optional_str(yd, 'decode', what)
        self.operation = get_optional_str(yd, 'operation', what)

        raw_syntax = get_optional_str(yd, 'syntax', what)
        if raw_syntax is not None:
            self.syntax = InsnSyntax.from_yaml(self.mnemonic,
                                               raw_syntax.strip())
        else:
            self.syntax = InsnSyntax.from_list([op.name
                                                for op in self.operands])

        pattern, op_to_grp = self.syntax.asm_pattern()
        self.asm_pattern = re.compile(pattern)
        self.pattern_op_to_grp = op_to_grp

        # Make sure we have exactly the operands we expect.
        if set(self.name_to_operand.keys()) != self.syntax.op_set:
            raise ValueError("Operand syntax for {!r} doesn't have the "
                             "same list of operands as given in the "
                             "operand list. The syntax uses {}, "
                             "but the list of operands gives {}."
                             .format(self.mnemonic,
                                     list(sorted(self.syntax.op_set)),
                                     list(sorted(self.name_to_operand))))

        encoding_yml = yd.get('encoding')
        self.encoding = None
        if encoding_yml is not None:
            self.encoding = Encoding(encoding_yml, encoding_schemes,
                                     self.name_to_operand, self.mnemonic)

        self.python_pseudo_op = check_bool(yd.get('python-pseudo-op', False),
                                           'python-pseudo-op flag for ' + what)
        if self.python_pseudo_op and self.encoding is not None:
            raise ValueError('{} specifies an encoding and also sets '
                             'python-pseudo-op.'.format(what))

        lpo = yd.get('literal-pseudo-op')
        if lpo is None:
            self.literal_pseudo_op = None
        else:
            lpo_lst = check_list(lpo, 'literal-pseudo-op flag for ' + what)
            for idx, item in enumerate(lpo_lst):
                if not isinstance(item, str):
                    raise ValueError('Item {} of literal-pseudo-op list for '
                                     '{} is {!r}, which is not a string.'
                                     .format(idx, what, item))
            self.literal_pseudo_op = cast(Optional[List[str]], lpo_lst)

            if self.python_pseudo_op:
                raise ValueError('{} specifies both python-pseudo-op and '
                                 'literal-pseudo-op.'
                                 .format(what))
            if self.encoding is not None:
                raise ValueError('{} specifies both an encoding and '
                                 'literal-pseudo-op.'
                                 .format(what))


def find_ambiguous_encodings(insns: List[Insn]) -> List[Tuple[str, str, int]]:
    '''Check for ambiguous instruction encodings

    Returns a list of ambiguous pairs (mnemonic0, mnemonic1, bits) where
    bits is a bit pattern that would match either instruction.

    '''
    masks = {}
    for insn in insns:
        if insn.encoding is not None:
            masks[insn.mnemonic] = insn.encoding.get_masks()

    ret = []
    for mnem0, mnem1 in itertools.combinations(masks.keys(), 2):
        m00, m01 = masks[mnem0]
        m10, m11 = masks[mnem1]

        # The pair of instructions is ambiguous if a bit pattern might be
        # either instruction. That happens if each bit index is either
        # allowed to be a 0 in both or allowed to be a 1 in both.
        # ambiguous_mask is the set of bits that don't distinguish the
        # instructions from each other.
        m0 = m00 & m10
        m1 = m01 & m11

        ambiguous_mask = m0 | m1
        if ambiguous_mask == (1 << 32) - 1:
            ret.append((mnem0, mnem1, m1 & ~m0))

    return ret


class InsnsFile:
    def __init__(self, yml: object) -> None:
        yd = check_keys(yml, 'top-level',
                        ['insn-groups', 'encoding-schemes', 'insns'],
                        [])

        self.groups = InsnGroups(yd['insn-groups'])
        self.encoding_schemes = EncSchemes(yd['encoding-schemes'])
        self.insns = [Insn(i, self.groups, self.encoding_schemes)
                      for i in check_list(yd['insns'], 'insns')]
        self.mnemonic_to_insn = index_list('insns', self.insns,
                                           lambda insn: insn.mnemonic.lower())

        ambiguous_encodings = find_ambiguous_encodings(self.insns)
        if ambiguous_encodings:
            ambiguity_msgs = []
            for mnem0, mnem1, bits in ambiguous_encodings:
                ambiguity_msgs.append('{!r} and {!r} '
                                      'both match bit pattern {:#010x}'
                                      .format(mnem0, mnem1, bits))
            raise ValueError('Ambiguous instruction encodings: ' +
                             ', '.join(ambiguity_msgs))

    def grouped_insns(self) -> List[Tuple[InsnGroup, List[Insn]]]:
        '''Return the instructions in groups'''
        grp_to_insns = {}  # type: Dict[str, List[Insn]]
        for insn in self.insns:
            grp_to_insns.setdefault(insn.group, []).append(insn)

        ret = []
        for grp in self.groups.groups:
            ret.append((grp, grp_to_insns.get(grp.key, [])))

        # We should have picked up all the instructions, because we checked
        # that each instruction has a valid group in the Insn constructor. Just
        # in case something went wrong, check that the counts match.
        gti_count = sum(len(insns) for insns in grp_to_insns.values())
        ret_count = sum(len(insns) for _, insns in ret)
        assert ret_count == gti_count

        return ret


def load_file(path: str) -> InsnsFile:
    '''Load the YAML file at path.

    Raises a RuntimeError on syntax or schema error.

    '''
    try:
        with open(path, 'r') as handle:
            return InsnsFile(yaml.load(handle, Loader=yaml.SafeLoader))
    except FileNotFoundError:
        raise RuntimeError('Cannot find YAML file at {!r}.'
                           .format(path)) from None
    except yaml.YAMLError as err:
        raise RuntimeError('Failed to parse YAML file at {!r}: {}'
                           .format(path, err)) from None
    except ValueError as err:
        raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                           .format(path, err)) from None
