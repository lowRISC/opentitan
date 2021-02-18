# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import random
from typing import Dict, List, Optional, Set

from shared.yaml_parse_helpers import (check_str, check_keys, check_list,
                                       load_yaml)


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

    def merge(self, other: 'Weights') -> None:
        for key in set(self.values.keys()) | set(other.values.keys()):
            self.values[key] = self.get(key) * other.get(key)


class Inheritance:
    '''One or more named parents, plus a weight'''
    def __init__(self, item_num: int, yml: object):
        if isinstance(yml, str):
            cfgs = yml
            weight = 1.0
        else:
            yd = check_keys(yml, 'parent', ['cfgs'], ['weight'])
            cfgs = check_str(yd['cfgs'],
                             'cfgs field for inheritance list {}'
                             .format(item_num))
            yw = yd.get('weight', 1.0)
            if isinstance(yw, float) or isinstance(yw, int):
                weight = float(yw)
            elif isinstance(yw, str):
                try:
                    weight = float(yw)
                except ValueError:
                    raise ValueError('The weight in inheritance list {} is '
                                     '{!r}, not a valid float.'
                                     .format(item_num, yw))
            else:
                raise ValueError('The weight in inheritance list {} is '
                                 'not a number or a string.'
                                 .format(item_num))

            if weight <= 0:
                raise ValueError('The weight in inheritance list {} is '
                                 '{}, which is not positive.'
                                 .format(item_num, weight))

        # cfgs should be a nonempty list of config names, separated by '+'
        # signs.
        if not cfgs:
            raise ValueError('Empty list of config names')

        self.names = cfgs.split('+')
        self.weight = weight

        # Check that each of the names in our list is nonempty (we'll get a
        # less confusing error if we spot that here)
        for n in self.names:
            if not n:
                raise ValueError('Empty name in list of config names: {}'
                                 .format(self.names))


class Config:
    '''An object representing configuration for a RIG run'''
    def __init__(self,
                 cfg_dir: str,
                 path: str,
                 known_names: Set[str],
                 yml: object):
        yd = check_keys(yml, 'top-level',
                        [],
                        ['gen-weights', 'insn-weights', 'inherit'])

        # The most general form for the inherit field is a list of dictionaries
        # that get parsed into Inheritance objects. As a shorthand, these
        # dictionaries can be represented strings (which implies a weight of
        # 1). As an even shorter shorthand, if you only have one possible
        # inheritance (so don't care about defining weights anyway), you can
        # represent it as just a string.
        y_inherit = yd.get('inherit', [])
        if isinstance(y_inherit, str):
            inherit_lst = [y_inherit]
        elif isinstance(y_inherit, list):
            inherit_lst = y_inherit
        else:
            raise ValueError('inherit field for config at {} '
                             'is not a string or list.'
                             .format(path))

        inhs = [Inheritance(idx + 1, elt)
                for idx, elt in enumerate(inherit_lst)]
        if not inhs:
            merged_ancestors = None
        else:
            # There's at least one possible list of parents. Pick one.
            parents = random.choices([i.names for i in inhs],
                                     weights=[i.weight for i in inhs])[0]
            # The Inheritance class constructor ensures that parents is
            # nonempty.
            assert parents
            merged_ancestors = Config.load_and_merge(cfg_dir,
                                                     parents, known_names)

        self.path = path
        self.gen_weights = Weights('gen-weights',
                                   yd.get('gen-weights', {}))
        self.insn_weights = Weights('insn-weights',
                                    yd.get('insn-weights', {}))

        if merged_ancestors is not None:
            self.merge(merged_ancestors)

    @staticmethod
    def load(cfg_dir: str,
             name: str,
             children: Optional[Set[str]] = None) -> 'Config':
        if children is not None and name in children:
            raise ValueError('Dependency loop for config: {} includes itself.'
                             .format(name))

        path = os.path.join(cfg_dir, name + '.yml')
        try:
            if children is None:
                known_names = {name}
            else:
                known_names = children | {name}

            return Config(cfg_dir, path, known_names, load_yaml(path, None))
        except ValueError as err:
            raise RuntimeError('Invalid schema in YAML file at {!r}: {}'
                               .format(path, err))

    @staticmethod
    def load_and_merge(cfg_dir: str,
                       names: List[str],
                       children: Set[str]) -> 'Config':
        assert names
        merged = Config.load(cfg_dir, names[0], children)
        for name in names[1:]:
            merged.merge(Config.load(cfg_dir, name, children))
        return merged

    def merge(self, other: 'Config') -> None:
        self.gen_weights.merge(other.gen_weights)
        self.insn_weights.merge(other.insn_weights)
