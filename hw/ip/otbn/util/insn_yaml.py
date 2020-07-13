# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Support code for reading the instruction database in insns.yml'''

import itertools
import re
from typing import (Callable, Dict, List, Optional,
                    Sequence, Set, Tuple, TypeVar, Union)

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


class BitRanges:
    '''Represents the bit ranges used for a field in an encoding scheme'''
    def __init__(self, as_string: str, what: str) -> None:
        #   ranges ::= range
        #            | range ',' ranges
        #
        #   range ::= num
        #           | num ':' num
        #
        # Ranges are assumed to be msb:lsb (with msb >= lsb). Bit indices are
        # at most 31 and ranges are disjoint.

        if not as_string:
            raise ValueError('Empty string as bits for {}'.format(what))

        overlaps = 0

        self.mask = 0
        self.ranges = []
        self.width = 0

        for rng in as_string.split(','):
            match = re.match(r'([0-9]+)(?:-([0-9]+))?$', rng)
            if match is None:
                raise ValueError('Range {!r} in bits for {} is malformed.'
                                 .format(rng, what))

            msb = int(match.group(1))
            maybe_lsb = match.group(2)
            lsb = msb if maybe_lsb is None else int(maybe_lsb)

            if msb < lsb:
                raise ValueError('Range {!r} in bits for {} has msb < lsb.'
                                 .format(rng, what))

            if msb >= 32:
                raise ValueError('Range {!r} in bits for {} has msb >= 32.'
                                 .format(rng, what))

            rng_mask = (1 << (msb + 1)) - (1 << lsb)
            overlaps |= rng_mask & self.mask
            self.mask |= rng_mask

            self.ranges.append((msb, lsb))
            self.width += msb - lsb + 1

        if overlaps:
            raise ValueError('Bits for {} have overlapping ranges '
                             '(mask: {:#08x})'
                             .format(what, overlaps))


class BoolLiteral:
    '''Represents a boolean literal, with possible 'x characters'''
    def __init__(self, as_string: str, what: str) -> None:
        # We represent this as 2 masks: "ones" and "x". The ones mask is the
        # bits that are marked 1. The x mask is the bits that are marked x.
        # Then you can test whether a particular value matches the literal by
        # zeroing all bits in the x mask and then comparing with the ones mask.
        self.ones = 0
        self.xs = 0
        self.width = 0

        # The literal should always start with a 'b'
        if not as_string.startswith('b'):
            raise ValueError("Boolean literal for {} doesn't start with a 'b'."
                             .format(what))

        for char in as_string[1:]:
            if char == '_':
                continue

            self.ones <<= 1
            self.xs <<= 1
            self.width += 1

            if char == '0':
                continue
            elif char == '1':
                self.ones |= 1
            elif char == 'x':
                self.xs |= 1
            else:
                raise ValueError('Boolean literal for {} has '
                                 'unsupported character: {!r}.'
                                 .format(what, char))

        if not self.width:
            raise ValueError('Empty boolean literal for {}.'.format(what))

    def char_for_bit(self, bit: int) -> str:
        '''Return 0, 1 or x for the bit at the given position'''
        assert bit < self.width
        if (self.ones >> bit) & 1:
            return '1'
        if (self.xs >> bit) & 1:
            return 'x'
        return '0'


class EncSchemeField:
    '''Represents a single field in an encoding scheme'''
    def __init__(self,
                 bits: BitRanges,
                 value: Optional[BoolLiteral],
                 shift: int) -> None:
        self.bits = bits
        self.value = value
        self.shift = shift

    @staticmethod
    def from_yaml(yml: object, what: str) -> 'EncSchemeField':
        # This is either represented as a dict in the YAML or as a bare string.
        bits_what = 'bits for {}'.format(what)
        value_what = 'value for {}'.format(what)
        shift_what = 'shift for {}'.format(what)

        shift = 0

        if isinstance(yml, dict):
            yd = check_keys(yml, what, ['bits'], ['value', 'shift'])

            bits_yml = yd['bits']
            if not (isinstance(bits_yml, str) or isinstance(bits_yml, int)):
                raise ValueError('{} is of type {}, not a string or int.'
                                 .format(bits_what, type(bits_yml).__name__))

            # We require value to be given as a string because it's supposed to
            # be in base 2, and PyYAML will parse 111 as one-hundred and
            # eleven, 011 as 9 and 0x11 as 17. Aargh!
            raw_value = None
            val_yml = yd.get('value')
            if val_yml is not None:
                if not isinstance(val_yml, str):
                    raise ValueError("{} is of type {}, but must be a string "
                                     "(we don't allow automatic conversion "
                                     "because YAML's int conversion assumes "
                                     "base 10 and value should be in base 2)."
                                     .format(value_what,
                                             type(val_yml).__name__))
                raw_value = val_yml

            # shift, on the other hand, is written in base 10. Allow an
            # integer.
            shift_yml = yd.get('shift')
            if shift_yml is None:
                pass
            elif isinstance(shift_yml, str):
                if not re.match(r'[0-9]+$', shift_yml):
                    raise ValueError('{} is {!r} but should be a '
                                     'non-negative integer.'
                                     .format(shift_what, shift_yml))
                shift = int(shift_yml)
            elif isinstance(shift_yml, int):
                if shift_yml < 0:
                    raise ValueError('{} is {!r} but should be a '
                                     'non-negative integer.'
                                     .format(shift_what, shift_yml))
                shift = shift_yml
            else:
                raise ValueError("{} is of type {}, but must be a string "
                                 "or non-negative integer."
                                 .format(shift_what, type(shift_yml).__name__))
        elif isinstance(yml, str) or isinstance(yml, int):
            bits_yml = yml
            raw_value = None
        else:
            raise ValueError('{} is a {}, but should be a '
                             'dict, string or integer.'
                             .format(what, type(yml).__name__))

        # The bits field is usually parsed as a string ("10-4", or similar).
        # But if it's a bare integer then YAML will parse it as an int. That's
        # fine, but we turn it back into a string to be re-parsed by BitRanges.
        assert isinstance(bits_yml, str) or isinstance(bits_yml, int)

        bits = BitRanges(str(bits_yml), bits_what)
        value = None
        if raw_value is not None:
            value = BoolLiteral(raw_value, value_what)
            if bits.width != value.width:
                raise ValueError('{} has bits that imply a width of {}, but '
                                 'a value with width {}.'
                                 .format(what, bits.width, value.width))

        return EncSchemeField(bits, value, shift)


class EncSchemeImport:
    '''An object representing inheritance of a parent scheme

    When importing a parent scheme, we can set some of its fields with
    immediate values. These are stored in the settings field.

    '''
    def __init__(self, yml: object, importer_name: str) -> None:
        as_str = check_str(yml,
                           'value for import in encoding scheme {!r}'
                           .format(importer_name))

        # The supported syntax is
        #
        #    - parent0(field0=b111, field1=b10)
        #    - parent1()
        #    - parent2

        match = re.match(r'([^ (]+)[ ]*(?:\(([^)]+)\))?$', as_str)
        if not match:
            raise ValueError('Malformed encoding scheme '
                             'inheritance by scheme {!r}: {!r}.'
                             .format(importer_name, as_str))

        self.parent = match.group(1)
        self.settings = {}  # type: Dict[str, BoolLiteral]

        when = ('When inheriting from {!r} in encoding scheme {!r}'
                .format(self.parent, importer_name))

        if match.group(2) is not None:
            args = match.group(2).split(',')
            for arg in args:
                arg = arg.strip()
                arg_parts = arg.split('=')
                if len(arg_parts) != 2:
                    raise ValueError('{}, found an argument with {} '
                                     'equals signs (should have exactly one).'
                                     .format(when, len(arg_parts) - 1))

                field_name = arg_parts[0]
                field_what = ('literal value for field {!r} when inheriting '
                              'from {!r} in encoding scheme {!r}'
                              .format(arg_parts[0], self.parent, importer_name))
                field_value = BoolLiteral(arg_parts[1], field_what)

                if field_name in self.settings:
                    raise ValueError('{}, found multiple arguments assigning '
                                     'values to the field {!r}.'
                                     .format(when, field_name))

                self.settings[field_name] = field_value

    def apply_settings(self,
                       esf: 'EncSchemeFields', what: str) -> 'EncSchemeFields':
        # Copy and set values in anything that has a setting
        fields = {}
        for name, literal in self.settings.items():
            old_field = esf.fields.get(name)
            if old_field is None:
                raise ValueError('{} sets unknown field {!r} from {!r}.'
                                 .format(what, name, self.parent))

            if old_field.bits.width != literal.width:
                raise ValueError('{} sets field {!r} from {!r} with a literal '
                                 'of width {}, but the field has width {}.'
                                 .format(what, name, self.parent,
                                         literal.width, old_field.bits.width))

            fields[name] = EncSchemeField(old_field.bits,
                                          literal,
                                          old_field.shift)

        # Copy anything else
        op_fields = set()
        for name, old_field in esf.fields.items():
            if name in fields:
                continue
            op_fields.add(name)
            fields[name] = old_field

        return EncSchemeFields(fields, op_fields, esf.mask)


class EncSchemeFields:
    '''An object representing some fields in an encoding scheme'''
    def __init__(self,
                 fields: Dict[str, EncSchemeField],
                 op_fields: Set[str],
                 mask: int) -> None:
        self.fields = fields
        self.op_fields = op_fields
        self.mask = mask

    @staticmethod
    def empty() -> 'EncSchemeFields':
        return EncSchemeFields({}, set(), 0)

    @staticmethod
    def from_yaml(yml: object, name: str) -> 'EncSchemeFields':
        if not isinstance(yml, dict):
            raise ValueError('fields for encoding scheme {!r} should be a '
                             'dict, but we saw a {}.'
                             .format(name, type(yml).__name__))

        fields = {}
        op_fields = set()  # type: Set[str]
        mask = 0

        overlaps = 0

        for key, val in yml.items():
            if not isinstance(key, str):
                raise ValueError('{!r} is a bad key for a field name of '
                                 'encoding scheme {} (should be str, not {}).'
                                 .format(key, name, type(key).__name__))

            fld_what = 'field {!r} of encoding scheme {}'.format(key, name)
            field = EncSchemeField.from_yaml(val, fld_what)

            overlaps |= mask & field.bits.mask
            mask |= field.bits.mask

            fields[key] = field
            if field.value is None:
                op_fields.add(key)

        if overlaps:
            raise ValueError('Direct fields for encoding scheme {} have '
                             'overlapping ranges (mask: {:#08x})'
                             .format(name, overlaps))

        return EncSchemeFields(fields, op_fields, mask)

    def merge_in(self, right: 'EncSchemeFields', when: str) -> None:
        for name, field in right.fields.items():
            if name in self.fields:
                raise ValueError('Duplicate field name: {!r} {}.'
                                 .format(name, when))

            overlap = self.mask & field.bits.mask
            if overlap:
                raise ValueError('Overlapping bit ranges '
                                 '(masks: {:08x} and {:08x} have '
                                 'intersection {:08x}) {}.'
                                 .format(self.mask,
                                         field.bits.mask, overlap, when))

            self.fields[name] = field
            self.mask |= field.bits.mask
            if field.value is None:
                assert name not in self.op_fields
                self.op_fields.add(name)


class EncScheme:
    def __init__(self, yml: object, name: str) -> None:
        what = 'encoding scheme {!r}'.format(name)
        yd = check_keys(yml, what, [], ['parents', 'fields'])

        if not yd:
            raise ValueError('{} has no parents or fields.'.format(what))

        fields_yml = yd.get('fields')
        self.direct_fields = (EncSchemeFields.from_yaml(fields_yml, name)
                              if fields_yml is not None
                              else EncSchemeFields.empty())

        parents_yml = yd.get('parents')
        parents_what = 'parents of {}'.format(what)
        parents = ([EncSchemeImport(y, name)
                    for y in check_list(parents_yml, parents_what)]
                   if parents_yml is not None
                   else [])
        self.parents = index_list(parents_what,
                                  parents,
                                  lambda imp: imp.parent)


class EncSchemes:
    def __init__(self, yml: object) -> None:
        if not isinstance(yml, dict):
            raise ValueError("value for encoding-schemes is expected to be "
                             "a dict, but was actually a {}."
                             .format(type(yml).__name__))

        self.schemes = {}  # type: Dict[str, EncScheme]
        self.resolved = {}  # type: Dict[str, EncSchemeFields]

        for key, val in yml.items():
            if not isinstance(key, str):
                raise ValueError('{!r} is a bad key for an encoding scheme '
                                 'name (should be str, not {}).'
                                 .format(key, type(key).__name__))
            self.schemes[key] = EncScheme(val, key)

    def _resolve(self,
                 name: str,
                 user: str,
                 stack: List[str]) -> EncSchemeFields:
        # Have we resolved this before?
        resolved = self.resolved.get(name)
        if resolved is not None:
            return resolved

        # Spot any circular inheritance
        if name in stack:
            raise RuntimeError('Circular inheritance of encoding '
                               'schemes: {}'
                               .format(' -> '.join(stack + [name])))

        # Does the scheme actually exist?
        scheme = self.schemes.get(name)
        if scheme is None:
            raise ValueError('{} requires undefined encoding scheme {!r}.'
                             .format(user, name))

        # Recursively try to resolve each parent scheme, applying any import
        # settings
        resolved_parents = {}
        new_stack = stack + [name]
        what = 'Import list of encoding scheme {!r}'.format(name)
        for pname, pimport in scheme.parents.items():
            resolved = self._resolve(pimport.parent, what, new_stack)
            resolved_parents[pname] = pimport.apply_settings(resolved, what)

        # Now try to merge the resolved imports
        merged = EncSchemeFields.empty()
        parent_names_so_far = []  # type: List[str]
        for pname, pfields in resolved_parents.items():
            when = ('merging fields of scheme {} into '
                    'already merged fields of {}'
                    .format(pname, ', '.join(parent_names_so_far)))
            merged.merge_in(pfields, when)
            parent_names_so_far.append(repr(pname))

        # Now try to merge in any direct fields
        when = ('merging direct fields of scheme {} into fields from parents'
                .format(name))
        merged.merge_in(scheme.direct_fields, when)

        return merged

    def resolve(self, name: str, mnemonic: str) -> EncSchemeFields:
        fields = self._resolve(name, 'Instruction {!r}'.format(mnemonic), [])

        # Check completeness
        missing = ((1 << 32) - 1) & ~fields.mask
        if missing:
            raise ValueError('Fields for encoding scheme {} miss some bits '
                             '(mask: {:#08x})'
                             .format(name, missing))

        return fields


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


class RegOperandType(OperandType):
    '''A class representing a register operand type'''
    TYPE_WIDTHS = {'gpr': 5, 'wdr': 5, 'csr': 12, 'wsr': 8}

    def __init__(self, reg_type: str, is_dest: bool):
        type_width = RegOperandType.TYPE_WIDTHS.get(reg_type)
        assert type_width is not None
        super().__init__(type_width)

        self.reg_type = reg_type
        self.is_dest = is_dest


class ImmOperandType(OperandType):
    '''A class representing an immediate operand type'''
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


class SyntaxToken:
    '''An object representing a single token in an instruction's syntax

    See InsnSyntax for more details. The is_literal attribute is true if this
    is a literal hunk of text (rather than an operand name). The text attribute
    either holds the literal syntax or the operand name.

    '''
    def __init__(self, is_literal: bool, text: str) -> None:
        assert text
        self.is_literal = is_literal
        # Make whitespace canonical for literals
        self.text = re.sub(r'\s+', ' ', text) if is_literal else text

    def render_doc(self) -> str:
        '''Return how this syntax token should look in the documentation'''
        if self.is_literal:
            return self.text
        else:
            return '<{}>'.format(self.text)


class SyntaxHunk:
    '''An object representing a hunk of syntax that might be optional'''
    def __init__(self,
                 is_optional: bool,
                 tokens: List[SyntaxToken],
                 operands: Set[str]) -> None:
        assert tokens
        self.is_optional = is_optional
        self.tokens = tokens
        self.operands = operands

    @staticmethod
    def from_list(operands: List[str]) -> 'SyntaxHunk':
        '''Smart constructor for a list of operands with "normal" syntax'''
        assert operands
        comma = SyntaxToken(True, ', ')
        tokens = [SyntaxToken(False, operands[0])]
        for op in operands[1:]:
            tokens.append(comma)
            tokens.append(SyntaxToken(False, op))

        op_set = set(operands)
        assert len(op_set) == len(operands)

        return SyntaxHunk(False, tokens, op_set)

    @staticmethod
    def from_string(mnemonic: str, optional: bool, raw: str) -> 'SyntaxHunk':
        '''Smart constructor that parses YAML syntax (see InsnSyntax)'''
        print('from_string({!r}, {!r}, {!r})'.format(mnemonic, optional, raw))
        assert raw

        tokens = []
        op_set = set()

        parts = re.split(r'<([^>]+)>', raw)
        for idx, part in enumerate(parts):
            # The matches for the regex appear in positions 1, 3, 5, ...
            is_literal = not (idx & 1)
            if ('<' in part or '>' in part) and not is_literal:
                raise ValueError("Syntax for {!r} has hunk {!r} which doesn't "
                                 "seem to surround <operand>s properly."
                                 .format(mnemonic, raw))

            if not is_literal:
                assert part
                if part in op_set:
                    raise ValueError("Syntax for {!r} has hunk {!r} with "
                                     "more than one occurrence of <{}>."
                                     .format(mnemonic, raw, part))
                op_set.add(part)

            # Only allow empty parts (and skip their tokens) if at one end or
            # the other
            if not part and idx not in [0, len(parts) - 1]:
                raise ValueError("Syntax for {!r} has two adjacent operand "
                                 "tokens, with no intervening syntax."
                                 .format(mnemonic))

            if part:
                tokens.append(SyntaxToken(is_literal, part))

        return SyntaxHunk(optional, tokens, op_set)

    def render_doc(self) -> str:
        '''Return how this hunk should look in the documentation'''
        parts = []
        for token in self.tokens:
            parts.append(token.render_doc())

        body = ''.join(parts)
        return '[{}]'.format(body) if self.is_optional else body


class InsnSyntax:
    '''A class representing the syntax of an instruction

    An instruction's syntax is specified in the YAML file by writing it out
    with operand names surrounded by angle brackets. For example, a simple NOT
    instruction might have a syntax of

        <dst>, <src>

    which should be interpreted as the following tokens:

        - Operand called 'dst'
        - A literal ','
        - Operand called 'src'

    Between the tokens, whitespace is optional (so "r0 , r1" and "r0,r1" both
    match the syntax above) unless a literal token is just a space, in which
    case some whitespace is required. For example

        <dst> <src>

    would match "r0 r1" but not "r0r1". Whitespace within literal syntax tokens
    means that some space is required, matching the regex \\s+. For example,
    the (rather strange) syntax

       <dst> + - <src>

    would match "r0 + - r1" or "r0+ -r1", but not "r0 +- r1".

    Some operands (and surrounding syntax) might be optional. The optional
    syntax is surrounded by square brackets. Nesting is not supported. For
    example:

       <dst>, <src>[, <offset>]

    would match "r0, r1, 123" or "r0, r1".

    Note that a given syntax might be ambiguous. For example,

       <dst>, <src>[, <offset>][, <flavour>]

    With "r0, r1, 123", is 123 an offset or a flavour? (We choose not to embed
    typing information into the syntax, because that results in very confusing
    assembler error messages). We break ties in the same way as the underlying
    regex engine, assigning the operand to the first group, so 123 is an offset
    in this case. Such syntaxes are rather confusing though, so probably not a
    good idea.

    The parsed syntax is stored as a list of "hunks". Each hunk contains a flag
    showing whether the hunk is optional or required and also a list of
    SyntaxToken objects.

    '''
    def __init__(self,
                 hunks: List[SyntaxHunk],
                 operands: Set[str]) -> None:
        self.hunks = hunks
        self.operands = operands

    @staticmethod
    def from_list(operands: List[str]) -> 'InsnSyntax':
        '''Smart constructor for a list of operands with "normal" syntax'''
        if not operands:
            return InsnSyntax([], set())

        hunk = SyntaxHunk.from_list(operands)
        return InsnSyntax([hunk], hunk.operands)

    @staticmethod
    def from_yaml(mnemonic: str, raw: str) -> 'InsnSyntax':
        '''Parse the syntax in the YAML file'''

        # The raw syntax looks something like
        #
        #    <op0>, <op1>[(<op2>)]
        #
        # to mean that you either have "r0, r1" or "r0, r2(r3)". First, split
        # out the bracketed parts.
        by_left = raw.split('[')
        parts = [(False, by_left[0])]
        for after_left in by_left[1:]:
            split = after_left.split(']', 1)
            if len(split) != 2:
                raise ValueError('Unbalanced or nested [] in instruction '
                                 'syntax for {!r}.'
                                 .format(mnemonic))

            parts += [(True, split[0]), (False, split[1])]

        # Now parts contains a list of pairs (required, txt) where txt is a
        # hunk of the syntax and req is true if this hunk is required. A part
        # might be empty. For example, "[a]b c[d]" with both lead and trail
        # with an empty part. But it shouldn't be empty if it's marked
        # optional: that would be something like "a[]b", which doesn't make
        # much sense.
        hunks = []
        for optional, raw in parts:
            if raw:
                hunks.append(SyntaxHunk.from_string(mnemonic, optional, raw))
            elif optional:
                raise ValueError('Empty [] in instruction syntax for {!r}.'
                                 .format(mnemonic))

        # Collect up operands across the hunks
        op_count = 0
        op_set = set()
        for hunk in hunks:
            op_count += len(hunk.operands)
            op_set |= hunk.operands

        if op_count != len(op_set):
            raise ValueError('Instruction syntax for {!r} is not '
                             'linear in its operands.'
                             .format(mnemonic))

        return InsnSyntax(hunks, op_set)

    def render_doc(self) -> str:
        '''Return how this syntax should look in the documentation'''
        return ''.join(hunk.render_doc() for hunk in self.hunks)


class EncodingField:
    '''A single element of an encoding's mapping'''
    def __init__(self,
                 value: Union[BoolLiteral, str],
                 scheme_field: EncSchemeField) -> None:
        self.value = value
        self.scheme_field = scheme_field

    @staticmethod
    def from_yaml(as_str: str,
                  scheme_field: EncSchemeField,
                  name_to_operand: Dict[str, Operand],
                  what: str) -> 'EncodingField':
        # The value should either be a boolean literal ("000xx11" or similar)
        # or should be a name, which is taken as the name of an operand.
        if not as_str:
            raise ValueError('Empty string as {}.'.format(what))

        # Set self.value to be either the bool literal or the name of the
        # operand.
        value_width = None
        value = ''  # type: Union[BoolLiteral, str]
        if re.match(r'b[01x_]+$', as_str):
            value = BoolLiteral(as_str, what)
            value_width = value.width
            value_type = 'a literal value'
        else:
            operand = name_to_operand.get(as_str)
            if operand is None:
                raise ValueError('Unknown operand, {!r}, as {}'
                                 .format(as_str, what))
            value_width = operand.op_type.width
            value = as_str
            value_type = 'an operand'

        # Unless we had an operand of type 'imm' (unknown width), we now have
        # an expected width. Check it matches the width of the schema field.
        if value_width is not None:
            if scheme_field.bits.width != value_width:
                raise ValueError('{} is mapped to {} with width {}, but the '
                                 'encoding schema field has width {}.'
                                 .format(what, value_type, value_width,
                                         scheme_field.bits.width))

        # Track the scheme field as well (so we don't have to keep track of a
        # scheme once we've made an encoding object)
        return EncodingField(value, scheme_field)


class Encoding:
    '''The encoding for an instruction'''
    def __init__(self,
                 yml: object,
                 schemes: EncSchemes,
                 name_to_operand: Dict[str, Operand],
                 mnemonic: str):
        what = 'encoding for instruction {!r}'.format(mnemonic)
        yd = check_keys(yml, what, ['scheme', 'mapping'], [])

        scheme_what = 'encoding scheme for instruction {!r}'.format(mnemonic)
        scheme_name = check_str(yd['scheme'], scheme_what)
        scheme_fields = schemes.resolve(scheme_name, mnemonic)

        what = 'encoding mapping for instruction {!r}'.format(mnemonic)

        # Check we've got exactly the right fields for the scheme
        ydm = check_keys(yd['mapping'], what, list(scheme_fields.op_fields), [])

        # Track the set of operand names that were used in some field
        operands_used = set()

        self.fields = {}
        for field_name, scheme_field in scheme_fields.fields.items():
            if scheme_field.value is not None:
                field = EncodingField(scheme_field.value, scheme_field)
            else:
                field_what = ('value for {} field in encoding for instruction {!r}'
                              .format(field_name, mnemonic))
                field = EncodingField.from_yaml(check_str(ydm[field_name], field_what),
                                                scheme_fields.fields[field_name],
                                                name_to_operand,
                                                field_what)

                # If the field's value is an operand rather than a literal, it
                # will have type str. Track the operands that we've used.
                if isinstance(field.value, str):
                    operands_used.add(field.value)

            self.fields[field_name] = field

        # We know that every field in the encoding scheme has a value. But we
        # still need to check that every operand ended up in some field.
        assert operands_used <= set(name_to_operand.keys())
        unused_ops = set(name_to_operand.keys()) - operands_used
        if unused_ops:
            raise ValueError('Not all operands used in {} (missing: {}).'
                             .format(what, ', '.join(list(unused_ops))))

    def get_masks(self) -> Tuple[int, int]:
        '''Return zeros/ones masks for encoding

        Returns a pair (m0, m1) where m0 is the "zeros mask": a mask where a
        bit is set if there is an bit pattern matching this encoding with that
        bit zero. m1 is the ones mask: equivalent, but for that bit one.

        '''
        m0 = 0
        m1 = 0
        for field_name, field in self.fields.items():
            if isinstance(field.value, str):
                m0 |= field.scheme_field.bits.mask
                m1 |= field.scheme_field.bits.mask
            else:
                # Match up the bits in the value with the ranges in the scheme.
                assert field.value.width > 0
                assert field.value.width == field.scheme_field.bits.width
                bits_seen = 0
                for msb, lsb in field.scheme_field.bits.ranges:
                    val_msb = field.scheme_field.bits.width - 1 - bits_seen
                    val_lsb = val_msb - msb + lsb
                    bits_seen += msb - lsb + 1

                    for idx in range(0, msb - lsb + 1):
                        desc = field.value.char_for_bit(val_lsb + idx)
                        if desc in ['0', 'x']:
                            m0 |= 1 << (idx + lsb)
                        if desc in ['1', 'x']:
                            m1 |= 1 << (idx + lsb)

        all_bits = (1 << 32) - 1
        assert (m0 | m1) == all_bits
        return (m0, m1)


class Insn:
    def __init__(self,
                 yml: object,
                 groups: InsnGroups,
                 encoding_schemes: EncSchemes) -> None:
        yd = check_keys(yml, 'instruction',
                        ['mnemonic', 'operands'],
                        ['group', 'rv32i', 'synopsis',
                         'syntax', 'doc', 'note', 'trailing-doc',
                         'decode', 'operation', 'encoding', 'glued-ops'])

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

        # Make sure we have exactly the operands we expect.
        if set(self.name_to_operand.keys()) != self.syntax.operands:
            raise ValueError("Operand syntax for {!r} doesn't have the "
                             "same list of operands as given in the "
                             "operand list. The syntax uses {}, "
                             "but the list of operands gives {}."
                             .format(self.mnemonic,
                                     list(sorted(self.syntax.operands)),
                                     list(sorted(self.name_to_operand))))

        encoding_yml = yd.get('encoding')
        self.encoding = None
        if encoding_yml is not None:
            self.encoding = Encoding(encoding_yml, encoding_schemes,
                                     self.name_to_operand, self.mnemonic)


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
                                           lambda insn: insn.mnemonic)

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
    except yaml.YAMLError as err:
        raise RuntimeError('Failed to parse YAML file at {!r}: {}'
                           .format(path, err)) from None
    except ValueError as err:
        raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                           .format(path, err)) from None
