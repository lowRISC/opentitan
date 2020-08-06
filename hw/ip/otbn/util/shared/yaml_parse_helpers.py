# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to help make typed objects out of parsed YAML'''

from typing import Callable, Dict, List, Optional, Sequence, TypeVar


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


def get_optional_str(data: Dict[str, object],
                     key: str, what: str) -> Optional[str]:
    return check_optional_str(data.get(key), '{} field for {}'.format(key, what))
