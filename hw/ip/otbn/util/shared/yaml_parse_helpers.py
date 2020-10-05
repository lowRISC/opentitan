# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code to help make typed objects out of parsed YAML'''

from typing import Callable, Dict, List, Optional, Sequence, TypeVar

import yaml
try:
    from yaml import CSafeLoader as YamlLoader
except ImportError:
    from yaml import SafeLoader as YamlLoader  # type: ignore


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
        raise ValueError('{} is of type {}, not a bool.'
                         .format(what, type(obj).__name__))
    return obj


def check_int(obj: object, what: str) -> int:
    '''Check that the given object is an integer

    If not, raise a ValueError; the what argument names the object.

    '''
    if not isinstance(obj, int):
        raise ValueError('{} is of type {}, not an integer.'
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


def load_yaml(path: str, what: Optional[str]) -> object:
    '''Load a YAML file at path.

    If there is no such file, or the file is not well-formed YAML, this raises
    a RuntimeError. If what is not None, it will be used in the error message.

    '''
    for_msg = ' for ' + what if what is not None else ''
    try:
        with open(path, 'r') as handle:
            return yaml.load(handle, Loader=YamlLoader)
    except FileNotFoundError:
        raise RuntimeError('Cannot find YAML file{} at {!r}.'
                           .format(for_msg, path)) from None
    except yaml.YAMLError as err:
        raise RuntimeError('Failed to parse YAML file{} at {!r}: {}'
                           .format(for_msg, path, err)) from None
