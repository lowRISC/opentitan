# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List

from reggen import register
from reggen.clocking import Clocking
from reggen.field import Field
from reggen.lib import check_keys, check_str, check_name, check_bool
from reggen.params import ReggenParams
from reggen.reg_base import RegBase
from reggen.register import Register

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
    ],
    'cdc': [
        's',
        "indicates the register must cross to a different "
        "clock domain before use.  The value shown here "
        "should correspond to one of the module's clocks."
    ],
})


class MultiRegister(RegBase):
    def __init__(self,
                 offset: int,
                 addrsep: int,
                 reg_width: int,
                 params: ReggenParams,
                 raw: object,
                 clocks: Clocking,
                 is_alias: bool):
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
        self.reg = Register.from_raw(reg_width, offset, params, reg_rd, clocks,
                                     is_alias)

        # The entire multi-reg block is always on the same clock
        # This is guaranteed by design
        self.async_name = self.reg.async_name
        self.async_clk = self.reg.async_clk

        self.sync_name = self.reg.sync_name
        self.sync_clk = self.reg.sync_clk

        self.cname = check_name(rd['cname'],
                                'cname field of multireg {}'
                                .format(self.reg.name))
        self.name = self.reg.name

        self.alias_target = None
        if is_alias:
            if 'alias_target' in rd:
                self.alias_target = check_name(rd['alias_target'],
                                               'name of alias target multiregister')
            else:
                raise ValueError('alias multiregister {} does not define the '
                                 'alias_target key.'
                                 .format(self.name))
        else:
            if 'alias_target' in rd:
                if rd['alias_target'] is not None:
                    raise ValueError('Illegal alias_target key in multiregister {} '
                                     '(this is not an alias register block).'
                                     .format(self.name))

        self.regwen_multi = check_bool(rd.get('regwen_multi', False),
                                       'regwen_multi field of multireg {}'
                                       .format(self.reg.name))

        default_compact = True if len(self.reg.fields) == 1 and not self.regwen_multi else False
        self.compact = check_bool(rd.get('compact', default_compact),
                                  'compact field of multireg {}'
                                  .format(self.reg.name))
        if self.compact and len(self.reg.fields) > 1:
            raise ValueError('Multireg {} sets the compact flag '
                             'but has multiple fields.'
                             .format(self.reg.name))

        if self.regwen_multi and self.compact:
            raise ValueError('Multireg {} sets the compact flag '
                             'but has regwen_multi set.'
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

        # dv_compact is true if the multireg can be equally divided, and we can
        # pack them as an array
        if self.count < regs_per_creg or (self.count % regs_per_creg) == 0:
            self.dv_compact = True
        else:
            self.dv_compact = False

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

    def needs_qe(self) -> bool:
        return self.reg.needs_qe()

    def _asdict(self) -> Dict[str, object]:
        rd = self.reg._asdict()
        rd['count'] = str(self.count)
        rd['cname'] = self.cname
        rd['regwen_multi'] = str(self.regwen_multi)
        rd['compact'] = str(self.compact)

        if self.alias_target is not None:
            rd['alias_target'] = self.alias_target

        return {'multireg': rd}

    def apply_alias(self, alias_reg: 'MultiRegister', where: str) -> None:
        '''Compare all attributes and replace overridable values.

        This ensures both registers are identical up to the overridable
        attributes like 'name', 'desc', 'resval' and 'tags'.
        '''
        # Attributes to be crosschecked
        attrs = ['async_name', 'async_clk', 'sync_name', 'sync_clk', 'count',
                 'regwen_multi', 'compact']
        for attr in attrs:
            if getattr(self, attr) != getattr(alias_reg, attr):
                raise ValueError('Value mismatch for attribute {} between '
                                 'alias multireg {} and multireg {} in {}.'
                                 .format(attr, self.name,
                                         alias_reg.name, where))

        # These attributes can be overridden by the aliasing mechanism.
        self.name = alias_reg.name
        self.cname = alias_reg.cname
        # We also keep track of the alias_target when overriding attributes.
        # This gives us a way to check whether a register has been overridden
        # or not, and what the name of the original register was.
        self.alias_target = alias_reg.alias_target

        # Then, update the template register.
        self.reg.apply_alias(alias_reg.reg, where)

        # Since the multireg structures must be identical, both generic and
        # alias reg must have the same amount of expanded regs at this point.
        assert (len(self.regs) == len(alias_reg.regs))
        # Finally, iterate over expanded regs and update them as well.
        for creg, alias_creg in zip(self.regs, alias_reg.regs):
            creg.apply_alias(alias_creg, where)

    def scrub_alias(self, where: str) -> None:
        '''Replaces sensitive fields in multiregister with generic names

        This function can be used to create the generic register descriptions
        from full alias hjson definitions. It will only work on registers
        where the alias_target keys are defined, and otherwise throw an error.
        '''
        # These attributes are scrubbed in the multireg.
        assert self.alias_target is not None
        self.name = self.alias_target
        self.cname = 'creg'
        self.alias_target = None

        # Then, update the template register.
        self.reg.scrub_alias(where)

        # Finally, iterate over expanded regs and scrub them as well.
        for creg in self.regs:
            creg.scrub_alias(where)
