# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List

from .lib import check_keys, check_str, check_list

# TO BE DEFINED
CM_ASSETS = [
    'FOO'
]

# TO BE DEFINED
CM_TYPES = [
    'BAR'
]


class CounterMeasure:
    """Object holding details for one countermeasure within an IP block."""

    def __init__(self, asset: str, cm_type: str, desc: str):
        self.asset = asset
        self.cm_type = cm_type
        self.desc = desc

    @staticmethod
    def from_raw(what: str, raw: object) -> 'CounterMeasure':
        """
        Create a CounterMeasure object from a dict.

        The 'raw' dict must have the keys 'name' and 'desc', where 'name' has
        to follow the canonical countermeasure naming convention.
        """
        rd = check_keys(raw, what, ['name', 'desc'], [])

        name = check_str(rd['name'], f'name field of {what}')
        desc = check_str(rd['desc'], f'desc field of {what}')

        try:
            asset, cm_type = name.split('.')
        except ValueError:
            raise ValueError(
                f'Invalid format: {name} ({what}).')

        if asset not in CM_ASSETS:
            raise ValueError(
                f'Invalid asset: {asset} ({what}).')

        if cm_type not in CM_TYPES:
            raise ValueError(
                f'Invalid type: {cm_type} ({what}).')
        return CounterMeasure(asset, cm_type, desc)

    @staticmethod
    def from_raw_list(what: str,
                      raw: object) -> List['CounterMeasure']:
        """
        Create a list of CounterMeasure objects from a list of dicts.

        The dicts in 'raw' must have the keys 'name' and 'desc', where 'name'
        has to follow the canonical countermeasure naming convention.
        """
        ret = []
        for idx, entry in enumerate(check_list(raw, what)):
            entry_what = f'entry {idx} of {what}'
            cm = CounterMeasure.from_raw(entry_what, entry)
            ret.append(cm)
        return ret

    def _asdict(self) -> Dict[str, object]:
        """Returns a dict with 'name' and 'desc' fields"""
        return {
            'name': str(self),
            'desc': self.desc
        }

    def __str__(self) -> str:
        return self.asset + '.' + self.cm_type
