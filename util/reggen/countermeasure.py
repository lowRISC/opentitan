# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
import logging as log
from typing import Dict, List, Sequence, Tuple

from reggen.lib import check_keys, check_str, check_list

# The documentation of assets and cm_types can be found here
# https://opentitan.org/book/doc/contributing/hw/comportability/#security-countermeasures
CM_ASSETS = [
    'KEY',
    'ADDR',
    'DATA_REG',
    'DATA_REG_SW',
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
    'REGWEN_MUBI',
    'REGREN',
    'SHADOW',
    'SCRAMBLE',
    'ADDR_INFECTION',
    'INTEGRITY',
    'READBACK',
    'ADDR_INFECTION',
    'CONSISTENCY',
    'DIGEST',
    'LC_GATED',
    'BKGN_CHK',
    'GLITCH_DETECT',
    'SW_UNREADABLE',
    'SW_UNWRITABLE',
    'SW_NOACCESS',
    'SIDELOAD',
    'SEC_WIPE',
    'SCA',
    'MASKING',
    'LOCAL_ESC',
    'GLOBAL_ESC',
    'UNPREDICTABLE',
    'TERMINAL',
    'COUNT',
    'CM'
]

# Tag to look for when extracting RTL annotations.
CM_RTL_TAG = 'SEC_CM:'


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
                f'Invalid countermeasure ID format: {name} ({what}).')
        if not re.fullmatch(r'^([a-zA-Z0-9_]*)', instance):
            raise ValueError(
                f'Invalid countermeasure instance name: {instance} ({what}).')
        if asset not in CM_ASSETS:
            raise ValueError(
                f'Invalid countermeasure asset: {asset} ({what}).')
        if cm_type not in CM_TYPES:
            raise ValueError(
                f'Invalid countermeasure type: {cm_type} ({what}).')
        return CounterMeasure(instance, asset, cm_type, desc)

    @staticmethod
    def from_raw_list(what: str, raw: object) -> List['CounterMeasure']:
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
        return {'name': str(self), 'desc': self.desc}

    def __str__(self) -> str:
        namestr = self.asset + '.' + self.cm_type
        return self.instance + '.' + namestr if self.instance else namestr

    @staticmethod
    def search_rtl_files(
            paths: Sequence[str]) -> Dict[str, List[Tuple[str, int]]]:
        """Find countermeasures in the given list of RTL files.

        The return value is a dictionary mapping countermeasure name to where
        that countermeasure is found (as a (path, line_number) pair).
        """
        ret: Dict[str, List[Tuple[str, int]]] = {}
        # Match things like "// SEC_CM: FOO" or "// SEC_CM: FOO, BAR"
        regex = re.compile(r'//\s*' + CM_RTL_TAG + r'\s*(.*)')
        good_name = re.compile(r'[A-Za-z0-9_.]+$')

        for path in paths:
            with open(path) as fd:
                for idx, line in enumerate(fd):
                    match = regex.search(line)
                    if not match:
                        continue

                    # We've got a hit. The regex above is intentionally lax
                    # because we want to see an error if someone writes
                    # something horrible, rather than silently ignoring the
                    # line. Split the match on commas to allow multiple entries
                    # on a line.
                    entries = match.group(1).split(',')
                    for entry in entries:
                        entry = entry.strip()

                        if not good_name.match(entry):
                            raise ValueError('Malformed countermeasure name, '
                                             '{!r}, at {}, line {}.'.format(
                                                 entry, path, idx + 1))
                        ret.setdefault(entry, []).append((path, idx + 1))

        return ret

    @staticmethod
    def check_annotation_list(block_name: str, hjson_path: str,
                              rtl_names: Dict[str, List[Tuple[str, int]]],
                              hjson_list: List['CounterMeasure']) -> bool:
        """Compare RTL to Hjson countermeasures.

        This compares a dictionary of countermeasure names extracted from the
        RTL against the list defined in the IP Hjson and checks that:
        - every name in the RTL should match one in Hjson
        - every entry in Hjson should have some matching name in the RTL

        Any mismatch logs an error showing the file and line of the problem.
        Returns True if there are no errors.
        """
        hjson_set = {str(cm) for cm in hjson_list}
        rtl_set = set(rtl_names.keys())

        # Is there anything in the RTL that doesn't correspond to an Hjson
        # entry?
        rtl_only_countermeasures = rtl_set - hjson_set
        for name in rtl_only_countermeasures:
            for rtl_path, line in rtl_names[name]:
                log.error(f"No Hjson countermeasure {name} exists for RTL "
                          f"reference at {rtl_path}, line {line}.")

        missing_countermeasures = hjson_set - rtl_set
        for name in missing_countermeasures:
            log.error(f"Hjson countermeasure {name} declared in Hjson file "
                      f"{hjson_path} doesn't appear in the RTL.")

        if len(rtl_only_countermeasures) > 0:
            if len(missing_countermeasures) > 0:
                log.error(f"Block {block_name}: Some unknown and some missing "
                          "countermeasures in RTL")
            else:
                log.error(f"Block {block_name}: Some unknown countermeasures "
                          "referenced in RTL.")
            return False
        elif len(missing_countermeasures) > 0:
            log.error(f"Block {block_name}: Some countermeasures in Hjson "
                      "don't appear in RTL.")
            return False
        return True
