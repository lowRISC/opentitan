# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Support code for reading the instruction database in insns.yml'''

import re
from typing import (Callable, Dict, List, Optional,
                    Sequence, Set, Tuple, TypeVar)

import yaml


T = TypeVar('T')


def check_keys(obj: object,
               what: str,
               required_keys: List[str],
               optional_keys: List[str]) -> Dict[str, object]:
    '''Check that obj is a dict object with the expected keys

    If not, raise a ValueError; the what argument names the object.

    '''
    if not isinstance(obj, dict):
        raise ValueError("{} is expected to be a dict, but was actually a {}."
                         .format(what, type(obj).__name__))

    allowed = set()
    missing = []
    for key in required_keys:
        assert key not in allowed
        allowed.add(key)
        if key not in obj:
            missing.append(key)

    for key in optional_keys:
        assert key not in allowed
        allowed.add(key)

    unexpected = []
    for key in obj:
        if key not in allowed:
            unexpected.append(key)

    if missing or unexpected:
        mstr = ('The following required fields were missing: {}.'
                .format(', '.join(missing)) if missing else '')
        ustr = ('The following unexpected fields were found: {}.'
                .format(', '.join(unexpected)) if unexpected else '')
        raise ValueError("{} doesn't have the right keys. {}{}{}"
                         .format(what,
                                 mstr,
                                 ' ' if mstr and ustr else '',
                                 ustr))

    return obj


def check_str(obj: object, what: str) -> str:
    '''Check that the given object is a string

    If not, raise a ValueError; the what argument names the object.

    '''
    if not isinstance(obj, str):
        raise ValueError('{} is of type {}, not a string.'
                         .format(what, type(obj).__name__))
    return obj


def check_optional_str(obj: object, what: str) -> Optional[str]:
    '''Check that the given object is a string or None

    If not, raise a ValueError; the what argument names the object.

    '''
    if obj is not None and not isinstance(obj, str):
        raise ValueError('{} is of type {}, not a string.'
                         .format(what, type(obj).__name__))
    return obj


def check_bool(obj: object, what: str) -> bool:
    '''Check that the given object is a bool

    If not, raise a ValueError; the what argument names the object.

    '''
    if obj is not True and obj is not False:
        raise ValueError('{} is of type {}, not a string.'
                         .format(what, type(obj).__name__))
    return obj


def check_list(obj: object, what: str) -> List[object]:
    '''Check that the given object is a list

    If not, raise a ValueError; the what argument names the object.

    '''
    if not isinstance(obj, list):
        raise ValueError('{} is of type {}, not a list.'
                         .format(what, type(obj).__name__))
    return obj


def index_list(what: str,
               objs: Sequence[T],
               get_key: Callable[[T], str]) -> Dict[str, T]:
    ret = {}
    for obj in objs:
        key = get_key(obj)
        if key in ret:
            raise ValueError('Duplicate object with key {} in {}.'
                             .format(key, what))
        ret[key] = obj
    return ret


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


class OperandType:
    '''The base class for some sort of operand type'''
    def __init__(self) -> None:
        pass

    def markdown_doc(self) -> Optional[str]:
        '''Generate any (markdown) documentation for this operand type

        The base class returns None, but subclasses might return something
        useful.

        '''
        return None


class RegOperandType(OperandType):
    '''A class representing a register operand type'''
    TYPES = ['gpr', 'wdr', 'csr', 'wsr']

    def __init__(self, reg_type: str, is_dest: bool):
        assert reg_type in RegOperandType.TYPES
        self.reg_type = reg_type
        self.is_dest = is_dest


class ImmOperandType(OperandType):
    '''A class representing an immediate operand type'''
    def __init__(self, width: Optional[int]):
        if width is not None:
            assert width > 0
        self.width = width

    def markdown_doc(self) -> Optional[str]:
        # Override from OperandType base class
        if self.width is None:
            return None

        return 'Valid range: `0..{}`'.format((1 << self.width) - 1)


class EnumOperandType(ImmOperandType):
    '''A class representing an enum operand type'''
    def __init__(self, items: List[str]):
        assert items
        super().__init__(int.bit_length(len(items) - 1))
        self.items = items

    def markdown_doc(self) -> Optional[str]:
        # Override from OperandType base class
        parts = ['Syntax table:\n\n'
                 '| Syntax | Value of immediate |\n'
                 '|--------|--------------------|\n']
        for idx, item in enumerate(self.items):
            parts.append('| `{}` | `{}` |\n'
                         .format(item, idx))
        return ''.join(parts)


class OptionOperandType(ImmOperandType):
    '''A class representing an option operand type'''
    def __init__(self, option: str):
        super().__init__(1)
        self.option = option

    def markdown_doc(self) -> Optional[str]:
        # Override from OperandType base class
        return 'To specify, use the literal syntax `{}`\n'.format(self.option)


def parse_operand_type(fmt: str) -> OperandType:
    '''Make sense of the operand type syntax'''
    # Registers
    if fmt == 'grs':
        return RegOperandType('gpr', False)
    if fmt == 'grd':
        return RegOperandType('gpr', True)
    if fmt == 'wrs':
        return RegOperandType('wdr', False)
    if fmt == 'wrd':
        return RegOperandType('wdr', True)
    if fmt == 'csr':
        return RegOperandType('csr', True)
    if fmt == 'wsr':
        return RegOperandType('wsr', True)

    # Immediates
    if fmt == 'imm':
        return ImmOperandType(None)
    m = re.match(r'imm([1-9][0-9]*)$', fmt)
    if m:
        return ImmOperandType(int(m.group(1)))
    m = re.match(r'enum\(([^\)]+)\)$', fmt)
    if m:
        return EnumOperandType([item.strip()
                                for item in m.group(1).split(',')])
    m = re.match(r'option\(([^\)]+)\)$', fmt)
    if m:
        return OptionOperandType(m.group(1).strip())

    raise ValueError("Operand type description {!r} "
                     "didn't match any recognised format."
                     .format(fmt))


def infer_operand_type(name: str) -> OperandType:
    '''Try to guess an operand's type from its name'''

    if re.match(r'grs[0-9]*$', name):
        return parse_operand_type('grs')
    if name in ['grd', 'wrd', 'csr', 'wsr']:
        return parse_operand_type(name)
    if re.match(r'wrs[0-9]*$', name):
        return parse_operand_type('wrs')
    if re.match(r'imm[0-9]*$', name):
        return parse_operand_type('imm')
    if name == 'offset':
        return parse_operand_type('imm')

    raise ValueError("Operand name {!r} doesn't imply an operand type: "
                     "you'll have to set the type explicitly."
                     .format(name))


def make_operand_type(yml: object, operand_name: str) -> OperandType:
    '''Construct a type for an operand

    This is either based on the type, if given, or inferred from the name
    otherwise.

    '''
    return (parse_operand_type(check_str(yml,
                                         'type for {} operand'
                                         .format(operand_name)))
            if yml is not None
            else infer_operand_type(operand_name))


def get_optional_str(data: Dict[str, object],
                     key: str, what: str) -> Optional[str]:
    return check_optional_str(data.get(key), '{} field for {}'.format(key, what))


class Operand:
    def __init__(self, yml: object, insn_name: str) -> None:
        # The YAML representation should be a string (a bare operand name) or a
        # dict.
        what = 'operand for {!r} instruction'.format(insn_name)
        if isinstance(yml, str):
            name = yml
            op_type = None
            doc = None
        elif isinstance(yml, dict):
            yd = check_keys(yml, what, ['name'], ['type', 'doc'])
            name = check_str(yd['name'], 'name of ' + what)

            op_what = '{!r} {}'.format(name, what)
            op_type = get_optional_str(yd, 'type', op_what)
            doc = get_optional_str(yd, 'doc', op_what)

        op_what = '{!r} {}'.format(name, what)
        self.name = name
        self.op_type = make_operand_type(op_type, name)
        self.doc = doc


class InsnSyntax:
    def __init__(self, raw: str) -> None:
        # The raw syntax looks something like "<foo> + <bar> (baz <qux>)". We
        # need to check that each <..> holds an operand name. We want to
        # tokenize the string to split out the operands. The easiest way to
        # encode this in the types is as a string followed by zero or more
        # pairs, (operand, string).
        #
        # Conveniently, re.split does exactly what we need, always yielding an
        # odd number of parts and starting with an empty string if there's a
        # match at the start.
        parts = re.split(r'<([^>]+)>', raw)
        self.prefix = parts[0]
        self.pairs = list(zip(parts[1::2], parts[2::2]))

        assert len(parts) == 1 + 2 * len(self.pairs)

        # Collect up the named operands that we've seen, checking for
        # duplicates
        self.operands = set()  # type: Set[str]
        for operand, _ in self.pairs:
            if operand in self.operands:
                raise ValueError('Instruction syntax ({!r}) has duplicate '
                                 'occurrence of the {!r} operand.'
                                 .format(raw, operand))
            self.operands.add(operand)

    def raw_string(self) -> str:
        '''Return the raw string of the syntax'''
        parts = [self.prefix]
        for operand, suffix in self.pairs:
            parts.append('<{}>'.format(operand))
            parts.append(suffix)
        return ''.join(parts)


class Insn:
    def __init__(self, yml: object, groups: InsnGroups) -> None:
        yd = check_keys(yml, 'instruction',
                        ['mnemonic', 'operands'],
                        ['group', 'rv32i', 'synopsis',
                         'syntax', 'doc', 'note', 'trailing-doc',
                         'decode', 'operation'])

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
        self.synopsis = get_optional_str(yd, 'synopsis', what)
        self.doc = get_optional_str(yd, 'doc', what)
        self.note = get_optional_str(yd, 'note', what)
        self.trailing_doc = get_optional_str(yd, 'trailing-doc', what)
        self.decode = get_optional_str(yd, 'decode', what)
        self.operation = get_optional_str(yd, 'operation', what)

        raw_syntax = get_optional_str(yd, 'syntax', what)
        self.syntax = None  # type: Optional[InsnSyntax]
        if raw_syntax is not None:
            self.syntax = InsnSyntax(raw_syntax)

            # Make sure we have exactly the operands we expect.
            if set(self.name_to_operand.keys()) != self.syntax.operands:
                raise ValueError("Operand syntax for {!r} doesn't have the "
                                 "same list of operands as given in the "
                                 "operand list. The syntax uses {}, "
                                 "but the list of operands gives {}."
                                 .format(self.mnemonic,
                                         list(sorted(self.syntax.operands)),
                                         list(sorted(self.name_to_operand))))


class InsnsFile:
    def __init__(self, yml: object) -> None:
        yd = check_keys(yml, 'top-level',
                        ['insn-groups', 'insns'],
                        [])

        self.groups = InsnGroups(yd['insn-groups'])
        self.insns = [Insn(i, self.groups)
                      for i in check_list(yd['insns'], 'insns')]
        self.mnemonic_to_insn = index_list('insns', self.insns,
                                           lambda insn: insn.mnemonic)

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
    except yaml.YAMLError as err:
        raise RuntimeError('Failed to parse YAML file at {!r}: {}'
                           .format(path, err)) from None
    except ValueError as err:
        raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                           .format(path, err)) from None
