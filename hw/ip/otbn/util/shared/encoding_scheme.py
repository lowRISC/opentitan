# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code for handling instruction encoding schemes'''

import re
from typing import Dict, List, Optional, Set

from .bit_ranges import BitRanges
from .bool_literal import BoolLiteral
from .yaml_parse_helpers import check_keys, check_str, check_list, index_list


class EncSchemeField:
    '''Represents a single field in an encoding scheme'''
    def __init__(self,
                 bits: BitRanges,
                 value: Optional[BoolLiteral]) -> None:
        self.bits = bits
        self.value = value

    @staticmethod
    def from_yaml(yml: object, what: str) -> 'EncSchemeField':
        # This is either represented as a dict in the YAML or as a bare string.
        bits_what = 'bits for {}'.format(what)
        value_what = 'value for {}'.format(what)

        if isinstance(yml, dict):
            yd = check_keys(yml, what, ['bits'], ['value'])

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

        bits = BitRanges.from_yaml(str(bits_yml), bits_what)
        value = None
        if raw_value is not None:
            value = BoolLiteral.from_string(raw_value, value_what)
            if bits.width != value.width:
                raise ValueError('{} has bits that imply a width of {}, but '
                                 'a value with width {}.'
                                 .format(what, bits.width, value.width))

        return EncSchemeField(bits, value)


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
                field_value = BoolLiteral.from_string(arg_parts[1], field_what)

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

            fields[name] = EncSchemeField(old_field.bits, literal)

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
