# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict

from shared.yaml_parse_helpers import check_keys, load_yaml


class Weights:
    '''An object representing a dict of weights, indexed by string'''
    def __init__(self, what: str, yml: object):
        if not isinstance(yml, dict):
            raise ValueError('{} is expected to be a dict, '
                             'but was actually a {}.'
                             .format(what, type(yml).__name__))

        self.values = {}  # type: Dict[str, float]
        for key, value in yml.items():
            if not isinstance(key, str):
                raise ValueError('{} had key {!r}, which is not a string.'
                                 .format(what, key))
            try:
                fval = float(value)
            except ValueError:
                raise ValueError('{} at key {!r} had value {!r}, '
                                 'which is not a float.'
                                 .format(what, key, value)) from None

            if fval < 0:
                raise ValueError('{} at key {!r} had negative value {}, '
                                 'which is not a valid weight.'
                                 .format(what, key, fval))

            self.values[key] = fval

    def get(self, key: str) -> float:
        '''Get a weight from the dictionary, defaulting to 1.0'''
        return self.values.get(key, 1.0)


class Config:
    '''An object representing configuration for a RIG run'''
    def __init__(self, path: str, yml: object):
        yd = check_keys(yml, 'top-level',
                        ['gen-weights'],
                        ['insn-weights'])

        self.path = path
        self.gen_weights = Weights('gen-weights', yd['gen-weights'])
        self.insn_weights = Weights('insn-weights',
                                    yd.get('insn-weights', {}))

    @staticmethod
    def load(path: str) -> 'Config':
        try:
            return Config(path, load_yaml(path, None))
        except ValueError as err:
            raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                               .format(path, err))
