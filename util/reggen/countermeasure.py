# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from typing import Dict, List

from .lib import check_keys, check_str, check_list

# The documentation of assets and cm_types can be found here
# https://docs.opentitan.org/doc/rm/comportability_specification/#countermeasures
CM_ASSETS = [
    'KEY',
    'ADDR',
    'DATA_REG',
    'CTRL_FLOW',
    'CTRL',
    'CONFIG',
    'LFSR',
    'RNG',
    'CTR',
    'FSM',
    'MEM',
    'CLK',
    'RST',
    'BUS',
    'INTERSIG',
    'MUX',
    'CONSTANTS',
    'STATE',
    'TOKEN',
    'LOGIC'
]

CM_TYPES = [
    'MUBI',
    'SPARSE',
    'DIFF',
    'REDUN',
    'REGWEN',
    'REGREN',
    'SHADOW',
    'SCRAMBLE',
    'INTEGRITY',
    'CONSISTENCY',
    'DIGEST',
    'LC_GATED',
    'BKGN_CHK',
    'GLITCH_DETECT',
    'SW_UNREADABLE',
    'SCA',
    'MASKING',
    'LOCAL_ESC',
    'GLOBAL_ESC'
]


class CounterMeasure:
    """Object holding details for one countermeasure within an IP block."""

    def __init__(self, instance: str, asset: str, cm_type: str, desc: str):
        self.instance = instance
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
            # the format is [CM_INST_NAME].<CM_ASSET>.<CM_TYPE>
            # i.e., the countermeasure instance name is optional.
            fields = name.split('.')
            if len(fields) == 3:
                instance, asset, cm_type = fields
            else:
                asset, cm_type = fields
                instance = ""
        except ValueError:
            raise ValueError(
                f'Invalid format: {name} ({what}).')
        if not re.fullmatch(r'^([a-zA-Z0-9_]*)', instance):
            raise ValueError(
                f'Invalid instance name: {instance} ({what}).')
        if asset not in CM_ASSETS:
            raise ValueError(
                f'Invalid asset: {asset} ({what}).')
        if cm_type not in CM_TYPES:
            raise ValueError(
                f'Invalid type: {cm_type} ({what}).')
        return CounterMeasure(instance, asset, cm_type, desc)

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
        namestr = self.asset + '.' + self.cm_type
        return self.instance + '.' + namestr if self.instance else namestr
