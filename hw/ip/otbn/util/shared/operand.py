# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from typing import List, Optional, Tuple

from .encoding import Encoding
from .encoding_scheme import EncSchemeField
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
        complicated looking expression, but it might be a sensible immediate"
        or "I don't know my width".

        On success, the value returned will be non-negative (2's complement
        encoded if a signed operand) and will fit in self.width bits. It will
        also already have been shifted if necessary.

        '''
        return None

    def render_val(self, value: int) -> str:
        '''Render the given value as a string.

        value should be a non-negative integer extracted from an encoding. The
        default implementation prints it as a decimal number. Register
        operands, for example, will want to print 3 as "x3" and so on.

        '''
        return str(value)

    def get_shift(self) -> int:
        '''Return shift used converting from asm representation to encoding'''
        return 0


class RegOperandType(OperandType):
    '''A class representing a register operand type'''
    TYPE_FMTS = {
        'gpr': (5, 'x'),
        'wdr': (5, 'w'),
        'csr': (12, None),
        'wsr': (8, None)
    }

    def __init__(self, reg_type: str, is_dest: bool) -> None:
        fmt = RegOperandType.TYPE_FMTS.get(reg_type)
        assert fmt is not None
        width, _ = fmt

        super().__init__(width)

        self.reg_type = reg_type
        self._is_dest = is_dest

    @staticmethod
    def make(reg_type: str,
             is_dest: bool,
             what: str,
             scheme_field: Optional[EncSchemeField]) -> 'RegOperandType':
        '''Sanity-checking smart constructor'''

        if scheme_field is not None:
            fmt = RegOperandType.TYPE_FMTS.get(reg_type)
            assert fmt is not None
            width, _ = fmt

            if scheme_field.bits.width != width:
                raise ValueError('In {}, there is an encoding scheme that '
                                 'allocates {} bits, but the operand has '
                                 'register type {!r}, which expects {} bits.'
                                 .format(what, scheme_field.bits.width,
                                         reg_type, width))

        return RegOperandType(reg_type, is_dest)

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

    def is_src(self) -> bool:
        '''True if this operand is considered a source'''
        return self.reg_type in ['csr', 'wsr'] or not self._is_dest

    def is_dest(self) -> bool:
        '''True if this operand is considered a destination'''
        return self._is_dest or self.reg_type in ['csr', 'wsr']


class ImmOperandType(OperandType):
    '''A class representing an immediate operand type'''
    def __init__(self,
                 width: Optional[int],
                 shift: int,
                 signed: bool) -> None:
        assert shift >= 0

        super().__init__(width)
        self.shift = shift
        self.signed = signed

    @staticmethod
    def make(width: Optional[int],
             shift: int,
             signed: bool,
             what: str,
             scheme_field: Optional[EncSchemeField]) -> 'ImmOperandType':
        '''Sanity-checking smart constructor'''

        if scheme_field is not None:
            # If there is an encoding scheme, check its width is compatible
            # with the operand type. If the operand type doesn't specify a
            # width, get one from the encoding scheme.
            if width is None:
                width = scheme_field.bits.width
            if scheme_field.bits.width != width:
                raise ValueError('In {}, there is an encoding scheme that '
                                 'allocates {} bits to the immediate operand '
                                 'but the operand claims to have width {}.'
                                 .format(what, scheme_field.bits.width, width))

        return ImmOperandType(width, shift, signed)

    def markdown_doc(self) -> Optional[str]:
        # Override from OperandType base class
        rng = self.get_range()
        if rng is None:
            return None

        lo, hi = rng
        if self.shift == 0:
            stp_msg = ''
        else:
            stp_msg = ' in steps of `{}`'.format(1 << self.shift)

        return 'Valid range: `{}..{}`{}'.format(lo, hi, stp_msg)

    def read_index(self, as_str: str) -> Optional[int]:
        # Give up immediately if we don't know our width
        if self.width is None:
            return None

        # Otherwise, try to parse the literal as an integer. Give up safely if
        # we can't decipher the immediate here.
        try:
            value = int(as_str)
        except ValueError:
            return None

        return self.encode_val(value)

    def render_val(self, value: int) -> str:
        # If this immediate is signed and we have a valid width, we need to
        # convert the value to a 2's-complement signed number. (There's not
        # much we can do if we don't know our width!)
        if self.signed and self.width is not None:
            assert (value >> self.width) == 0
            assert self.width >= 1
            if value >> (self.width - 1):
                value -= 1 << self.width
                assert value < 0

        return str(value << self.shift)

    def get_shift(self) -> int:
        assert self.shift >= 0
        return self.shift

    def get_range(self) -> Optional[Tuple[int, int]]:
        '''Return the range of values representable by this operand

        Returns None if the operand has no width. Subclasses might override
        this. Note that if self.shift is nonzero, not every value in the range
        is necessarily representable.

        '''
        if self.width is None:
            return None

        if self.signed:
            lo = -((1 << self.width) // 2)
            hi = max(-(lo + 1), 0)
        else:
            lo = 0
            hi = (1 << self.width) - 1

        return (lo << self.shift, hi << self.shift)

    def encode_val(self, value: int) -> int:
        '''Encode this value by shifting and as 2's complement if necessary.

        The result is always non-negative. The value should be representable by
        this operand (width, shift and sign), otherwise this raises a ValueError.

        '''
        assert self.width is not None

        # First, try to shift right. Check that we won't clobber any low bits.
        shift_mask = (1 << self.shift) - 1
        if (value & shift_mask) != 0:
            raise ValueError('Cannot encode the value {}: the operand has a '
                             'shift of {}, but that would clobber some bits '
                             '(because {} & {} = {}, not zero).'
                             .format(value, self.shift,
                                     value, shift_mask, value & shift_mask))

        shifted = value >> self.shift

        rng = self.get_range()
        assert rng is not None
        lo, hi = rng

        if not (lo <= shifted <= hi):
            shifted_msg = (', which shifts down to {}'.format(shifted)
                           if self.shift != 0 else '')
            raise ValueError('Cannot encode the value {}{} as a {}-bit '
                             '{}signed value. Possible range: {}..{}.'
                             .format(value, shifted_msg,
                                     self.width,
                                     '' if self.signed else 'un',
                                     lo, hi))

        if self.signed:
            encoded = (1 << self.width) + shifted if shifted < 0 else shifted
        else:
            assert shifted >= 0
            encoded = shifted

        assert (encoded >> self.width) == 0
        return encoded


class EnumOperandType(ImmOperandType):
    '''A class representing an enum operand type'''
    def __init__(self,
                 items: List[str],
                 what: str,
                 scheme_field: Optional[EncSchemeField]) -> None:
        assert items

        # The number of items gives a minimum width for the field. If there is
        # an encoding, use that width, but check that it's enough to hold all
        # the items.
        min_width = int.bit_length(len(items) - 1)
        if scheme_field is None:
            width = min_width
        else:
            if scheme_field.bits.width < min_width:
                raise ValueError('In {}, there is an encoding scheme that '
                                 'assigns {} bits to the field. But this '
                                 'field is an enum with {} items, so needs '
                                 'at least {} bits.'
                                 .format(what, scheme_field.bits.width,
                                         len(items), min_width))
            width = scheme_field.bits.width

        super().__init__(width, 0, False)
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

    def get_range(self) -> Optional[Tuple[int, int]]:
        return (0, len(self.items) - 1)


class OptionOperandType(ImmOperandType):
    '''A class representing an option operand type'''
    def __init__(self,
                 option: str,
                 what: str,
                 scheme_field: Optional[EncSchemeField]) -> None:

        width = 1
        if scheme_field is not None:
            assert width <= scheme_field.bits.width
            width = scheme_field.bits.width

        super().__init__(width, 0, False)
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

    def get_range(self) -> Optional[Tuple[int, int]]:
        return (0, 1)


def parse_operand_type(fmt: str,
                       what: str,
                       scheme_field: Optional[EncSchemeField]) -> OperandType:
    '''Make sense of the operand type syntax'''
    # Registers
    if fmt == 'grs':
        return RegOperandType.make('gpr', False, what, scheme_field)
    if fmt == 'grd':
        return RegOperandType.make('gpr', True, what, scheme_field)
    if fmt == 'wrs':
        return RegOperandType.make('wdr', False, what, scheme_field)
    if fmt == 'wrd':
        return RegOperandType.make('wdr', True, what, scheme_field)
    if fmt == 'csr':
        return RegOperandType.make('csr', True, what, scheme_field)
    if fmt == 'wsr':
        return RegOperandType.make('wsr', True, what, scheme_field)

    # Immediates
    for base, signed in [('simm', True), ('uimm', False)]:
        # The type of an immediate operand is encoded as
        #
        #   BASE WIDTH? (<<SHIFT)?
        #
        # where BASE is 'simm' or 'uimm', WIDTH is a positive integer and SHIFT
        # is a non-negative integer. The regex below captures WIDTH as group 1
        # and SHIFT as group 2.
        m = re.match(base + r'([1-9][0-9]*)?(?:<<([0-9]+))?$', fmt)
        if m is not None:
            width = int(m.group(1)) if m.group(1) is not None else None
            shift = int(m.group(2)) if m.group(2) is not None else 0
            return ImmOperandType.make(width, shift, signed,
                                       what, scheme_field)

    m = re.match(r'enum\(([^\)]+)\)$', fmt)
    if m:
        return EnumOperandType([item.strip()
                                for item in m.group(1).split(',')],
                               what, scheme_field)
    m = re.match(r'option\(([^\)]+)\)$', fmt)
    if m:
        return OptionOperandType(m.group(1).strip(), what, scheme_field)

    raise ValueError("Operand type description {!r} "
                     "didn't match any recognised format."
                     .format(fmt))


def infer_operand_type(name: str,
                       what: str,
                       scheme_field: Optional[EncSchemeField]) -> OperandType:
    '''Try to guess an operand's type from its name'''

    if re.match(r'grs[0-9]*$', name):
        return parse_operand_type('grs', what, scheme_field)
    if name in ['grd', 'wrd', 'csr', 'wsr']:
        return parse_operand_type(name, what, scheme_field)
    if re.match(r'wrs[0-9]*$', name):
        return parse_operand_type('wrs', what, scheme_field)
    if re.match(r'imm[0-9]*$', name):
        return parse_operand_type('simm', what, scheme_field)
    if name == 'offset':
        return parse_operand_type('simm', what, scheme_field)

    raise ValueError("Operand name {!r} doesn't imply an operand type: "
                     "you'll have to set the type explicitly."
                     .format(name))


def make_operand_type(yml: object,
                      operand_name: str,
                      mnemonic: str,
                      scheme_field: Optional[EncSchemeField]) -> OperandType:
    '''Construct a type for an operand

    This is either based on the type, if given, or inferred from the name
    otherwise. If scheme_field is not None, this is the encoding scheme field
    that will be used.

    '''
    what = ('the type for the {!r} operand of instruction {!r}'
            .format(operand_name, mnemonic))
    return (parse_operand_type(check_str(yml, what), what, scheme_field)
            if yml is not None
            else infer_operand_type(operand_name, what, scheme_field))


class Operand:
    def __init__(self,
                 yml: object,
                 mnemonic: str,
                 insn_encoding: Optional[Encoding]) -> None:
        # The YAML representation should be a string (a bare operand name) or a
        # dict.
        what = 'operand for {!r} instruction'.format(mnemonic)
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

        # If there is an encoding, look up the encoding scheme field that
        # corresponds to this operand.
        enc_scheme_field = None
        if insn_encoding is not None:
            field_name = insn_encoding.op_to_field_name.get(name)
            if field_name is None:
                raise ValueError('The {!r} instruction has an operand called '
                                 '{!r}, but the associated encoding has no '
                                 'field that encodes it.'
                                 .format(mnemonic, name))
            enc_scheme_field = insn_encoding.fields[field_name].scheme_field

        self.name = name
        self.op_type = make_operand_type(op_type, name,
                                         mnemonic, enc_scheme_field)
        self.doc = doc
