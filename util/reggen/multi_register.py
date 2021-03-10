# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List

from reggen import register
from .field import Field
from .lib import check_keys, check_str, check_name, check_bool
from .params import ReggenParams
from .reg_base import RegBase
from .register import Register

REQUIRED_FIELDS = {
    'name': ['s', "base name of the registers"],
    'desc': ['t', "description of the registers"],
    'count': [
        's', "number of instances to generate."
        " This field can be integer or string matching"
        " from param_list."
    ],
    'cname': [
        's', "base name for each instance, mostly"
        " useful for referring to instance in messages."
    ],
    'fields': [
        'l', "list of register field description"
        " groups. Describes bit positions used for"
        " base instance."
    ]
}
OPTIONAL_FIELDS = register.OPTIONAL_FIELDS.copy()
OPTIONAL_FIELDS.update({
    'regwen_multi': [
        'pb', "If true, regwen term increments"
        " along with current multireg count."
    ],
    'compact': [
        'pb', "If true, allow multireg compacting."
        "If false, do not compact."
    ]
})


class MultiRegister(RegBase):
    def __init__(self,
                 offset: int,
                 addrsep: int,
                 reg_width: int,
                 params: ReggenParams,
                 raw: object):
        super().__init__(offset)

        rd = check_keys(raw, 'multireg',
                        list(REQUIRED_FIELDS.keys()),
                        list(OPTIONAL_FIELDS.keys()))

        # Now that we've checked the schema of rd, we make a "reg" version of
        # it that removes any fields that are allowed by MultiRegister but
        # aren't allowed by Register. We'll pass that to the register factory
        # method.
        reg_allowed_keys = (set(register.REQUIRED_FIELDS.keys()) |
                            set(register.OPTIONAL_FIELDS.keys()))
        reg_rd = {key: value
                  for key, value in rd.items()
                  if key in reg_allowed_keys}
        self.reg = Register.from_raw(reg_width, offset, params, reg_rd)

        self.cname = check_name(rd['cname'],
                                'cname field of multireg {}'
                                .format(self.reg.name))

        self.regwen_multi = check_bool(rd.get('regwen_multi', False),
                                       'regwen_multi field of multireg {}'
                                       .format(self.reg.name))

        default_compact = True if len(self.reg.fields) == 1 else False
        self.compact = check_bool(rd.get('compact', default_compact),
                                  'compact field of multireg {}'
                                  .format(self.reg.name))
        if self.compact and len(self.reg.fields) > 1:
            raise ValueError('Multireg {} sets the compact flag '
                             'but has multiple fields.'
                             .format(self.reg.name))

        count_str = check_str(rd['count'],
                              'count field of multireg {}'
                              .format(self.reg.name))
        self.count = params.expand(count_str,
                                   'count field of multireg ' + self.reg.name)
        if self.count <= 0:
            raise ValueError("Multireg {} has a count of {}, "
                             "which isn't positive."
                             .format(self.reg.name, self.count))

        # Generate the registers that this multireg expands into. Here, a
        # "creg" is a "compacted register", which might contain multiple actual
        # registers.
        if self.compact:
            assert len(self.reg.fields) == 1
            width_per_reg = self.reg.fields[0].bits.msb + 1
            assert width_per_reg <= reg_width
            regs_per_creg = reg_width // width_per_reg
        else:
            regs_per_creg = 1

        self.regs = []
        creg_count = (self.count + regs_per_creg - 1) // regs_per_creg
        for creg_idx in range(creg_count):
            min_reg_idx = regs_per_creg * creg_idx
            max_reg_idx = min(min_reg_idx + regs_per_creg, self.count) - 1
            creg_offset = offset + creg_idx * addrsep

            reg = self.reg.make_multi(reg_width,
                                      creg_offset, creg_idx, creg_count,
                                      self.regwen_multi, self.compact,
                                      min_reg_idx, max_reg_idx, self.cname)
            self.regs.append(reg)

    def next_offset(self, addrsep: int) -> int:
        return self.offset + len(self.regs) * addrsep

    def get_n_bits(self, bittype: List[str] = ["q"]) -> int:
        return sum(reg.get_n_bits(bittype) for reg in self.regs)

    def get_field_list(self) -> List[Field]:
        ret = []
        for reg in self.regs:
            ret += reg.get_field_list()
        return ret

    def is_homogeneous(self) -> bool:
        return self.reg.is_homogeneous()

    def _asdict(self) -> Dict[str, object]:
        rd = self.reg._asdict()
        rd['count'] = str(self.count)
        rd['cname'] = self.cname
        rd['regwen_multi'] = str(self.regwen_multi)
        rd['compact'] = str(self.compact)

        return {'multireg': rd}
