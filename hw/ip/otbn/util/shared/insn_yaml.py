# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Support code for reading the instruction database in insns.yml'''

import itertools
import os
import re
from typing import Dict, List, Optional, Tuple, cast

from .encoding import Encoding
from .encoding_scheme import EncSchemes
from .lsu_desc import LSUDesc
from .operand import Operand
from .syntax import InsnSyntax
from .yaml_parse_helpers import (check_keys, check_str, check_bool, check_int,
                                 check_list, index_list, get_optional_str,
                                 load_yaml)


class Insn:
    def __init__(self,
                 yml: object,
                 encoding_schemes: Optional[EncSchemes]) -> None:
        yd = check_keys(yml, 'instruction',
                        ['mnemonic', 'operands'],
                        ['group', 'rv32i', 'synopsis',
                         'syntax', 'doc', 'note', 'trailing-doc',
                         'encoding', 'glued-ops',
                         'literal-pseudo-op', 'python-pseudo-op', 'lsu',
                         'straight-line', 'cycles'])

        self.mnemonic = check_str(yd['mnemonic'], 'mnemonic for instruction')

        what = 'instruction with mnemonic {!r}'.format(self.mnemonic)

        encoding_yml = yd.get('encoding')
        self.encoding = None
        if encoding_yml is not None:
            if encoding_schemes is None:
                raise ValueError('{} specifies an encoding, but the file '
                                 'didn\'t specify any encoding schemes.'
                                 .format(what))

            self.encoding = Encoding(encoding_yml,
                                     encoding_schemes, self.mnemonic)

        self.operands = [Operand(y, self.mnemonic, self.encoding)
                         for y in check_list(yd['operands'],
                                             'operands for ' + what)]
        self.name_to_operand = index_list('operands for ' + what,
                                          self.operands,
                                          lambda op: op.name)

        # The call to index_list has checked that operand names are distinct.
        # We also need to check that no operand abbreviation clashes with
        # anything else.
        operand_names = set(self.name_to_operand.keys())
        for op in self.operands:
            if op.abbrev is not None:
                if op.abbrev in operand_names:
                    raise ValueError('The name {!r} appears as an operand or '
                                     'abbreviation more than once for '
                                     'instruction {!r}.'
                                     .format(op.abbrev, self.mnemonic))
                operand_names.add(op.abbrev)

        if self.encoding is not None:
            # If we have an encoding, we passed it to the Operand constructors
            # above. This ensured that each operand has a field. However, it's
            # possible that there are some operand names the encoding mentions
            # that don't actually have an operand. Check for that here.
            missing_ops = (set(self.encoding.op_to_field_name.keys()) -
                           set(self.name_to_operand.keys()))
            if missing_ops:
                raise ValueError('Encoding scheme for {} specifies '
                                 'some non-existent operands: {}.'
                                 .format(what, ', '.join(list(missing_ops))))

        self.rv32i = check_bool(yd.get('rv32i', False),
                                'rv32i flag for ' + what)
        self.glued_ops = check_bool(yd.get('glued-ops', False),
                                    'glued-ops flag for ' + what)
        self.synopsis = get_optional_str(yd, 'synopsis', what)
        self.doc = get_optional_str(yd, 'doc', what)
        self.note = get_optional_str(yd, 'note', what)
        self.trailing_doc = get_optional_str(yd, 'trailing-doc', what)

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

        lsu_yaml = yd.get('lsu', None)
        if lsu_yaml is None:
            self.lsu = None
        else:
            self.lsu = LSUDesc.from_yaml(lsu_yaml,
                                         'lsu field for {}'.format(what))
            for idx, op_name in enumerate(self.lsu.target):
                if op_name not in self.name_to_operand:
                    raise ValueError('element {} of the target for the lsu '
                                     'field for {} is {!r}, which is not a '
                                     'operand name of the instruction.'
                                     .format(idx, what, op_name))

        self.straight_line = yd.get('straight-line', True)

        self.cycles = check_int(yd.get('cycles', 1),
                                'cycles field for ' + what)
        if self.cycles <= 0:
            raise ValueError('cycles field for {} is not positive.'
                             .format(what))

    def enc_vals_to_op_vals(self,
                            cur_pc: int,
                            enc_vals: Dict[str, int]) -> Dict[str, int]:
        '''Convert values extracted from an encoding to their logical values

        This converts between "encoded values" and "operand values" (as defined
        in the OperandType class).

        The enc_vals dictionary should be keyed by the instruction's operand
        names (guaranteed by Encoding.extract_operands). This function should
        only be called when every operand has a width (which will definitely be
        the case if we just decoded these values from an instruction word).

        '''
        op_vals = {}
        for op_name, enc_val in enc_vals.items():
            op_type = self.name_to_operand[op_name].op_type
            op_val = op_type.enc_val_to_op_val(enc_val, cur_pc)
            # This assertion should hold because OperandType.enc_val_to_op_val
            # doesn't return None if the operand type has a width and the
            # function is given a PC.
            assert op_val is not None
            op_vals[op_name] = op_val
        return op_vals

    def disassemble(self,
                    cur_pc: int,
                    op_vals: Dict[str, int]) -> str:
        '''Return disassembly for this instruction

        op_vals should be a dictionary mapping operand names to operand values
        (not encoded values). mnem_width is the width to pad the mnemonic to.

        '''
        hunks = self.syntax.render(cur_pc, op_vals, self.name_to_operand)
        mnem = self.mnemonic
        if hunks and self.glued_ops:
            mnem += hunks[0] + ' '
            hunks = hunks[1:]
        else:
            mnem += ' '

        if len(mnem) < 15:
            mnem += ' ' * (15 - len(mnem))

        # The lstrip here deals with a tricky corner case for instructions like
        # bn.mulqacc if the .z option isn't supplied. In that case, the syntax
        # for the operands starts with a space (following the optional .z that
        # isn't there) and would mess up our alignment.
        return mnem + ''.join(hunks).lstrip()


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


class InsnGroup:
    def __init__(self,
                 path: str,
                 encoding_schemes: Optional[EncSchemes],
                 yml: object) -> None:

        yd = check_keys(yml, 'insn-group',
                        ['key', 'title', 'doc', 'insns'], [])
        self.key = check_str(yd['key'], 'insn-group key')
        self.title = check_str(yd['title'], 'insn-group title')
        self.doc = check_str(yd['doc'], 'insn-group doc')

        insns_what = 'insns field for {!r} instruction group'.format(self.key)
        insns_rel_path = check_str(yd['insns'], insns_what)
        insns_path = os.path.normpath(os.path.join(os.path.dirname(path),
                                                   insns_rel_path))
        insns_yaml = load_yaml(insns_path, insns_what)
        try:
            self.insns = [Insn(i, encoding_schemes)
                          for i in check_list(insns_yaml, insns_what)]
        except ValueError as err:
            raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                               .format(insns_path, err)) from None


class InsnGroups:
    def __init__(self,
                 path: str,
                 encoding_schemes: Optional[EncSchemes],
                 yml: object) -> None:
        self.groups = [InsnGroup(path, encoding_schemes, y)
                       for y in check_list(yml, 'insn-groups')]
        if not self.groups:
            raise ValueError('Empty list of instruction groups: '
                             'we need at least one as a base group.')
        self.key_to_group = index_list('insn-groups',
                                       self.groups, lambda ig: ig.key)


class InsnsFile:
    def __init__(self, path: str, yml: object) -> None:
        yd = check_keys(yml, 'top-level',
                        ['insn-groups'],
                        ['encoding-schemes'])

        enc_scheme_path = get_optional_str(yd, 'encoding-schemes', 'top-level')
        if enc_scheme_path is None:
            self.encoding_schemes = None
        else:
            src_dir = os.path.dirname(path)
            es_path = os.path.normpath(os.path.join(src_dir, enc_scheme_path))
            es_yaml = load_yaml(es_path, 'encoding schemes')
            try:
                self.encoding_schemes = EncSchemes(es_yaml)
            except ValueError as err:
                raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                                   .format(es_path, err)) from None

        self.groups = InsnGroups(path,
                                 self.encoding_schemes,
                                 yd['insn-groups'])

        # The instructions are grouped by instruction group and stored in
        # self.groups. Most of the time, however, we just want "an OTBN
        # instruction" and don't care about the group. Retrieve them here.
        self.insns = []
        for grp in self.groups.groups:
            self.insns += grp.insns

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
        return [(grp, grp.insns) for grp in self.groups.groups]


def load_file(path: str) -> InsnsFile:
    '''Load the YAML file at path.

    Raises a RuntimeError on syntax or schema error.

    '''
    try:
        return InsnsFile(path, load_yaml(path, None))
    except ValueError as err:
        raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                           .format(path, err)) from None


_DEFAULT_INSNS_FILE = None  # type: Optional[InsnsFile]


def load_insns_yaml() -> InsnsFile:
    '''Load the insns.yml file from its default location.

    Caches its result. Raises a RuntimeError on syntax or schema error.

    '''
    global _DEFAULT_INSNS_FILE
    if _DEFAULT_INSNS_FILE is None:
        dirname = os.path.dirname(__file__)
        rel_path = os.path.join('..', '..', 'data', 'insns.yml')
        insns_yml = os.path.normpath(os.path.join(dirname, rel_path))
        _DEFAULT_INSNS_FILE = load_file(insns_yml)

    return _DEFAULT_INSNS_FILE
