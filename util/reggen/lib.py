# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
'''Parsing support code for reggen'''

import re
from typing import Dict, List, Optional, cast

# Names that are prohibited (used as reserved keywords in systemverilog)
_VERILOG_KEYWORDS = {
    'alias', 'always', 'always_comb', 'always_ff', 'always_latch', 'and',
    'assert', 'assign', 'assume', 'automatic', 'before', 'begin', 'bind',
    'bins', 'binsof', 'bit', 'break', 'buf', 'bufif0', 'bufif1', 'byte',
    'case', 'casex', 'casez', 'cell', 'chandle', 'class', 'clocking', 'cmos',
    'config', 'const', 'constraint', 'context', 'continue', 'cover',
    'covergroup', 'coverpoint', 'cross', 'deassign', 'default', 'defparam',
    'design', 'disable', 'dist', 'do', 'edge', 'else', 'end', 'endcase',
    'endclass', 'endclocking', 'endconfig', 'endfunction', 'endgenerate',
    'endgroup', 'endinterface', 'endmodule', 'endpackage', 'endprimitive',
    'endprogram', 'endproperty', 'endspecify', 'endsequence', 'endtable',
    'endtask', 'enum', 'event', 'expect', 'export', 'extends', 'extern',
    'final', 'first_match', 'for', 'force', 'foreach', 'forever', 'fork',
    'forkjoin', 'function', 'generate', 'genvar', 'highz0', 'highz1', 'if',
    'iff', 'ifnone', 'ignore_bins', 'illegal_bins', 'import', 'incdir',
    'include', 'initial', 'inout', 'input', 'inside', 'instance', 'int',
    'integer', 'interface', 'intersect', 'join', 'join_any', 'join_none',
    'large', 'liblist', 'library', 'local', 'localparam', 'logic', 'longint',
    'macromodule', 'matches', 'medium', 'modport', 'module', 'nand', 'negedge',
    'new', 'nmos', 'nor', 'noshowcancelled', 'not', 'notif0', 'notif1', 'null',
    'or', 'output', 'package', 'packed', 'parameter', 'pmos', 'posedge',
    'primitive', 'priority', 'program', 'property', 'protected', 'pull0',
    'pull1', 'pulldown', 'pullup', 'pulsestyle_onevent', 'pulsestyle_ondetect',
    'pure', 'rand', 'randc', 'randcase', 'randsequence', 'rcmos', 'real',
    'realtime', 'ref', 'reg', 'release', 'repeat', 'return', 'rnmos', 'rpmos',
    'rtran', 'rtranif0', 'rtranif1', 'scalared', 'sequence', 'shortint',
    'shortreal', 'showcancelled', 'signed', 'small', 'solve', 'specify',
    'specparam', 'static', 'string', 'strong0', 'strong1', 'struct', 'super',
    'supply0', 'supply1', 'table', 'tagged', 'task', 'this', 'throughout',
    'time', 'timeprecision', 'timeunit', 'tran', 'tranif0', 'tranif1', 'tri',
    'tri0', 'tri1', 'triand', 'trior', 'trireg', 'type', 'typedef', 'union',
    'unique', 'unsigned', 'use', 'uwire', 'var', 'vectored', 'virtual', 'void',
    'wait', 'wait_order', 'wand', 'weak0', 'weak1', 'while', 'wildcard',
    'wire', 'with', 'within', 'wor', 'xnor', 'xor'
}


def check_str_dict(obj: object, what: str) -> Dict[str, object]:
    if not isinstance(obj, dict):
        raise ValueError(
            f"{what} is expected to be a dict, but was actually a "
            f"{type(obj).__name__}.")

    for key in obj:
        if not isinstance(key, str):
            raise ValueError(
                f'{what} has a key {key!r}, which is not a string.')

    return cast(Dict[str, object], obj)


def check_keys(obj: object, what: str, required_keys: List[str],
               optional_keys: List[str]) -> Dict[str, object]:
    '''Check that obj is a dict object with the expected keys

    If not, raise a ValueError; the what argument names the object.
    '''
    od = check_str_dict(obj, what)

    allowed = set()
    missing = []
    for key in required_keys:
        assert key not in allowed
        allowed.add(key)
        if key not in od:
            missing.append(key)

    for key in optional_keys:
        assert key not in allowed
        allowed.add(key)

    unexpected = []
    for key in od:
        if key not in allowed:
            unexpected.append(key)

    if missing or unexpected:
        mstr = ('The following required fields were missing: '
                f'{", ".join(missing)}.') if missing else ''
        ustr = ('The following unexpected fields were found: '
                f'{", ".join(unexpected)}.') if unexpected else ''
        raise ValueError(f"{what} doesn't have the right keys. "
                         f"{mstr}{' ' if mstr and ustr else ''}{ustr}")

    return od


def check_str(obj: object, what: str) -> str:
    '''Check that the given object is a string

    If not, raise a ValueError; the what argument names the object.
    '''
    if not isinstance(obj, str):
        raise ValueError(
            f'{what} is of type {type(obj).__name__}, not a string.')
    return obj


def check_name(obj: object, what: str) -> str:
    '''Check that obj is a string that's a valid name.

    If not, raise a ValueError; the what argument names the object.
    '''
    as_str = check_str(obj, what)

    # Allow the usual symbol constituents (alphanumeric plus underscore; no
    # leading numbers)
    if not re.match(r'[a-zA-Z_][a-zA-Z_0-9]*$', as_str):
        raise ValueError(f"{what} is {as_str!r}, which isn't a valid symbol "
                         "in C / Verilog, so isn't allowed as a name.")

    # Also check that this isn't a reserved word.
    if as_str in _VERILOG_KEYWORDS:
        raise ValueError(f"{what} is {as_str!r}, which is a reserved word in "
                         "SystemVerilog, so isn't allowed as a name.")

    return as_str


def check_bool(obj: object, what: str) -> bool:
    '''Check that obj is a bool or a string that parses to a bool.

    If not, raise a ValueError; the what argument names the object.

    '''
    if isinstance(obj, str):
        as_bool = {
            'true': True,
            'false': False,
            '1': True,
            '0': False
        }.get(obj.lower())
        if as_bool is None:
            raise ValueError(
                f'{what} is {obj!r}, which cannot be parsed as a bool.')
        return as_bool

    if obj is True or obj is False:
        return obj

    raise ValueError(f'{what} is of type {type(obj).__name__}, not a bool.')


def check_list(obj: object, what: str) -> List[object]:
    '''Check that the given object is a list

    If not, raise a ValueError; the what argument names the object.
    '''
    if not isinstance(obj, list):
        raise ValueError(
            f'{what} is of type {type(obj).__name__}, not a list.')
    return obj


def check_str_list(obj: object, what: str) -> List[str]:
    '''Check that the given object is a list of strings

    If not, raise a ValueError; the what argument names the object.
    '''
    lst = check_list(obj, what)
    for idx, elt in enumerate(lst):
        if not isinstance(elt, str):
            raise ValueError(
                f'Element {idx} of {what} is of type {type(elt).__name__}, '
                'not a string.')
    return cast(List[str], lst)


def check_int(obj: object, what: str) -> int:
    '''Check that obj is an integer or a string that parses to an integer.

    If not, raise a ValueError; the what argument names the object.
    '''
    if isinstance(obj, int):
        return obj

    if isinstance(obj, str):
        try:
            return int(obj, 0)
        except ValueError:
            raise ValueError(
                f'{what} is {obj!r}, which cannot be parsed as an int.'
            ) from None

    raise ValueError(
        f'{what} is of type {type(obj).__name__}, not an integer.')


def check_xint(obj: object, what: str) -> Optional[int]:
    '''Check that obj is an integer, a string that parses to an integer or "x".

    On success, return an integer value if there is one or None if the value
    was 'x'. On failure, raise a ValueError; the what argument names the
    object.
    '''
    if isinstance(obj, int):
        return obj

    if isinstance(obj, str):
        if obj == 'x':
            return None
        try:
            return int(obj, 0)
        except ValueError:
            raise ValueError(
                f'{what} is {obj!r}, which is not "x", nor can it be parsed '
                'as an int.')

    raise ValueError(
        f'{what} is of type {type(obj).__name__}, not an integer.')


def check_optional_str(obj: object, what: str) -> Optional[str]:
    '''Check that obj is a string or None'''
    return None if obj is None else check_str(obj, what)


def check_optional_bool(obj: object, what: str) -> Optional[bool]:
    '''Check that obj is a bool or None'''
    return None if obj is None else check_bool(obj, what)


def check_optional_name(obj: object, what: str) -> Optional[str]:
    '''Check that obj is a valid name or None'''
    return None if obj is None else check_name(obj, what)


def get_basename(name: str) -> str:
    '''Strip trailing _number (used as multireg suffix) from name'''
    # TODO: This is a workaround, should solve this as part of parsing a
    # multi-reg.
    match = re.search(r'_[0-9]+$', name)
    assert match
    assert match.start() > 0
    return name[0:match.start()]
