# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict

from .lib import check_keys, check_str, check_int

REQUIRED_FIELDS = {
    'name': ['s', "name of the member of the enum"],
    'desc': ['t', "description when field has this value"],
    'value': ['d', "value of this member of the enum"]
}


class EnumEntry:
    def __init__(self, where: str, max_val: int, raw: object):
        rd = check_keys(raw, where,
                        list(REQUIRED_FIELDS.keys()),
                        [])

        self.name = check_str(rd['name'], 'name field of {}'.format(where))
        self.desc = check_str(rd['desc'], 'desc field of {}'.format(where))
        self.value = check_int(rd['value'], 'value field of {}'.format(where))
        if not (0 <= self.value <= max_val):
            raise ValueError("value for {} is {}, which isn't representable "
                             "in the field (representable range: 0 .. {})."
                             .format(where, self.value, max_val))

    def _asdict(self) -> Dict[str, object]:
        return {
            'name': self.name,
            'desc': self.desc,
            'value': str(self.value)
        }
