# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from typing import List, Optional
from .yaml_parse_helpers import check_keys, check_str, get_optional_str


class OperandType:
    '''The base class for some sort of operand type'''
    def __init__(self, width: Optional[int]) -> None:
        assert width is None or width > 0
        self.width = width

    def markdown_doc(self) -> Optional[str]:
        '''Generate any (markdown) documentation for this operand type

        The base class returns None, but subclasses might return something
        useful.

        '''
        return None

    def syntax_determines_value(self) -> bool:
        '''Can the value of this operand always be inferred from asm syntax?

        This is true for things like registers (the value "5" only comes from
        "r5", for example), but false for arbitrary immediates: an immediate
        operand might have a value that comes from a relocation.

        '''
        return False

    def read_index(self, as_str: str) -> Optional[int]:
        '''Try to read the given syntax as an actual integer index

        Raises a ValueError on definite failure ("found cabbage when I expected
        a register name"). Returns None on a soft failure: "this is a
        complicated looking expression, but it might be a sensible immediate".

        '''
        return None

    def render_val(self, value: int) -> str:
        '''Render the given value as a string.

        The default implementation prints it as a decimal number. Register
        operands, for example, will want to print 3 as "x3" and so on.

        '''
        return str(value)


class RegOperandType(OperandType):
    '''A class representing a register operand type'''
    TYPE_FMTS = {
        'gpr': (5, 'x'),
        'wdr': (5, 'w'),
        'csr': (12, None),
        'wsr': (8, None)
    }

    def __init__(self, reg_type: str, is_dest: bool):
        fmt = RegOperandType.TYPE_FMTS.get(reg_type)
        assert fmt is not None
        width, _ = fmt
        super().__init__(width)

        self.reg_type = reg_type
        self.is_dest = is_dest

    def syntax_determines_value(self) -> bool:
        return True

    def read_index(self, as_str: str) -> int:
        width, pfx = RegOperandType.TYPE_FMTS[self.reg_type]

        re_pfx = '' if pfx is None else re.escape(pfx)
        match = re.match(re_pfx + '([0-9]+)$', as_str)
        if match is None:
            raise ValueError("Expression {!r} can't be parsed as a {}."
                             .format(as_str, self.reg_type))

        idx = int(match.group(1))
        assert 0 <= idx
        if idx >> width:
            raise ValueError("Invalid register of type {}: {!r}."
                             .format(self.reg_type, as_str))

        return idx

    def render_val(self, value: int) -> str:
        fmt = RegOperandType.TYPE_FMTS.get(self.reg_type)
        assert fmt is not None
        _, pfx = fmt

        if pfx is None:
            return super().render_val(value)

        return '{}{}'.format(pfx, value)


class ImmOperandType(OperandType):
    '''A class representing an immediate operand type'''
    def markdown_doc(self) -> Optional[str]:
        # Override from OperandType base class
        if self.width is None:
            return None

        return 'Valid range: `0..{}`'.format((1 << self.width) - 1)

    def read_index(self, as_str: str) -> Optional[int]:
        # We only support simple integer literals.
        try:
            return int(as_str)
        except ValueError:
            return None


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

    def syntax_determines_value(self) -> bool:
        return True

    def read_index(self, as_str: str) -> Optional[int]:
        for idx, item in enumerate(self.items):
            if as_str == item:
                return idx

        known_vals = ', '.join(repr(item) for item in self.items)
        raise ValueError('Invalid enum value, {!r}. '
                         'Supported values: {}.'
                         .format(as_str, known_vals))

    def render_val(self, value: int) -> str:
        # On a bad value, we have to return *something*. Since this is just
        # going into disassembly, let's be vaguely helpful and return something
        # that looks clearly bogus.
        #
        # Note that if the number of items in the enum is not a power of 2,
        # this could happen with a bad binary, despite good tools.
        if value < 0 or value >= len(self.items):
            return '???'

        return self.items[value]


class OptionOperandType(ImmOperandType):
    '''A class representing an option operand type'''
    def __init__(self, option: str):
        super().__init__(1)
        self.option = option

    def markdown_doc(self) -> Optional[str]:
        # Override from OperandType base class
        return 'To specify, use the literal syntax `{}`\n'.format(self.option)

    def syntax_determines_value(self) -> bool:
        return True

    def read_index(self, as_str: str) -> Optional[int]:
        if as_str == self.option:
            return 1

        raise ValueError('Invalid option value, {!r}. '
                         'If specified, it should have been {!r}.'
                         .format(as_str, self.option))

    def render_val(self, value: int) -> str:
        # Option types are always 1 bit wide, so the value should be 0 or 1.
        assert value in [0, 1]
        return self.option if value else ''


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
