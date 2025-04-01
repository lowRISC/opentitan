# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List

from reggen.lib import check_keys, check_str, check_list, check_name


class Feature:
    """Object holding details for one feature within an IP block."""

    def __init__(self, instance: str, name: str, desc: str):
        self.instance = instance
        self.name = name
        self.desc = desc

    @staticmethod
    def from_raw(what: str, raw: object) -> 'Feature':
        """
        Create a Feature object from a dict.

        The 'raw' dict must have the keys 'name' and 'desc', where 'name' has
        to follow the canonical feature naming convention.
        """
        rd = check_keys(raw, what, ['name', 'desc'], [])

        name = check_str(rd['name'], f'name field of {what}')
        desc = check_str(rd['desc'], f'desc field of {what}')

        try:
            # the format is [INST_NAME].<feature>
            # i.e., the IP instance name is optional.
            fields = name.split('.', 1)
            if len(fields) == 1:
                instance = ""
                name = fields[0]
            elif len(fields) == 2:
                instance, name = fields
        except ValueError:
            raise ValueError(f'Invalid feature ID format: {name} ({what}).')

        name = name.replace('.', '_').replace('-', '_')
        name = check_name(name, f'name of {what}')

        return Feature(instance, name, desc)

    @staticmethod
    def from_raw_list(what: str, raw: object) -> List['Feature']:
        """
        Create a list of Feature objects from a list of dicts.

        The dicts in 'raw' must have the keys 'name' and 'desc', where 'name'
        has to follow the canonical feature naming convention.
        """
        ret = []
        for idx, entry in enumerate(check_list(raw, what)):
            entry_what = f'entry {idx} of {what}'
            cm = Feature.from_raw(entry_what, entry)
            ret.append(cm)
        return ret

    def _asdict(self) -> Dict[str, object]:
        """Returns a dict with 'name' and 'desc' fields"""
        return {'name': str(self), 'desc': self.desc}

    def __str__(self) -> str:
        return f'{self.instance}.{self.name}' if self.instance else self.name
