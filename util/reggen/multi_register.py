# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Optional

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
    'compact':
    ['pb', "If true, allow multireg compacting."
     "If false, do not compact."],
    'cdc': [
        's', "indicates the register must cross to a different clock domain "
        "before use.  The value shown here should correspond to one of the "
        "module's clocks."
    ],
})


class MultiRegister(RegBase):
    """One or more copies of an underlying register.

    Instance variables:

      reg          Represents the underlying register itself

      cname        The basename used for the concrete registers that make up
                   the multiregister.

      regwen_multi If this is true, each of the copies of the replicated
                   register has its own regwen.

      compact      If this is true, multiple copies of the replicated register
                   might share a concrete register.

      count        The number of copies of the replicated register.

      cregs        The concrete registers that make up the multiregister.
                   These will each contain at least one copy of the replicated
                   register.

      dv_compact   If this is true then the concrete registers in the
                   multi-register are all identical (either because there is
                   only one concrete register or because the replicated copies
                   of reg divide evenly into a whole number of concrete
                   registers).
    """

    def __init__(self,
                 name: str,
                 offset: int,
                 alias_target: Optional[str],
                 reg: Register,
                 cname: str,
                 regwen_multi: bool,
                 compact: bool,
                 dv_compact: bool,
                 count: int,
                 cregs: List[Register]):
        super().__init__(name, offset,
                         reg.async_name, reg.async_clk,
                         reg.sync_name, reg.sync_clk, alias_target)
        self.reg = reg
        self.cname = cname
        self.regwen_multi = regwen_multi
        self.compact = compact
        self.dv_compact = dv_compact
        self.count = count
        self.cregs = cregs

    @staticmethod
    def from_raw(raw: object, reg_width: int, offset: int, addrsep: int,
                 params: ReggenParams, clocks: Clocking, is_alias: bool) -> 'MultiRegister':
        '''Create a MultiRegister object from a dictionary.

        The underlying register block has registers with reg_width bits and the
        first concrete register in the expanded multi-register should be at the
        given offset.

        The concrete registers are spaced addrsep bytes apart and the params
        and clocks values get passed to the constructor for the underlying
        register that gets replicated.

        If is_alias is true then this is supposed to alias some
        (multi-)register and we expect the dictionary in raw to define
        alias_target.
        '''

        # Check the raw object is a dictionary that has the right keys to
        # describe a MultiRegister.
        rd = check_keys(raw, 'multireg',
                        list(REQUIRED_FIELDS.keys()),
                        list(OPTIONAL_FIELDS.keys()))

        # Now that we've checked the schema of rd, we make a "reg" version of
        # it that removes any fields that are allowed by MultiRegister but
        # aren't allowed by Register. We'll pass that to the register factory
        # method.
        reg_allowed_keys = (set(register.REQUIRED_FIELDS.keys()) |
                            set(register.OPTIONAL_FIELDS.keys()))
        reg_rd = {
            key: value
            for key, value in rd.items() if key in reg_allowed_keys
        }

        preg = Register.from_raw(reg_width, offset, params, reg_rd, clocks,
                                is_alias)

        name = check_name(rd['name'], 'name of multi-register')

        alias_target = None
        if is_alias:
            if 'alias_target' in rd:
                alias_target = check_name(rd['alias_target'],
                                          'name of alias target multiregister')
            else:
                raise ValueError(f'alias multiregister {name} does not define '
                                 f'the alias_target key.')
        else:
            if 'alias_target' in rd:
                if rd['alias_target'] is not None:
                    raise ValueError(f'Illegal alias_target key in '
                                     f'multiregister {name} (this is not an '
                                     f'alias register block).')

        cname = check_name(rd['cname'], f'cname field of multireg {name}')
        regwen_multi = check_bool(rd.get('regwen_multi', False),
                                  f'regwen_multi field of multireg {name}')

        default_compact = len(preg.fields) == 1 and not regwen_multi
        compact = check_bool(rd.get('compact', default_compact),
                             f'compact field of multireg {name}')

        if compact:
            if len(preg.fields) > 1:
                raise ValueError(f'Multireg {name} sets the compact flag '
                                 'but has multiple fields.')
            if regwen_multi:
                raise ValueError(f'Multireg {name} sets the compact flag '
                                 'but has regwen_multi set.')

        count_str = check_str(rd['count'], f'count field of multireg {name}')
        count = params.expand(count_str, f'count field of multireg {name}')

        if count <= 0:
            raise ValueError(f"Multireg {name} has a count of {count}, "
                             "which isn't positive.")

        # Generate the registers that this multireg expands into. Here, a
        # "creg" is a "compacted register", which might contain multiple actual
        # registers.
        if compact:
            assert len(preg.fields) == 1
            width_per_reg = preg.fields[0].bits.msb + 1
            assert width_per_reg <= reg_width
            regs_per_creg = reg_width // width_per_reg
        else:
            regs_per_creg = 1

        cregs = []
        creg_count = (count + regs_per_creg - 1) // regs_per_creg
        for creg_idx in range(creg_count):
            min_reg_idx = regs_per_creg * creg_idx
            max_reg_idx = min(min_reg_idx + regs_per_creg, count) - 1
            creg_offset = offset + creg_idx * addrsep

            creg = preg.make_multi(reg_width,
                                   creg_offset, creg_idx, creg_count,
                                   regwen_multi, compact,
                                   min_reg_idx, max_reg_idx, cname)
            cregs.append(creg)

        # dv_compact is true if the multireg can be equally divided, and we can
        # pack them as an array
        dv_compact = (count < regs_per_creg or (count % regs_per_creg) == 0)

        return MultiRegister(name, offset, alias_target,
                             preg, cname, regwen_multi,
                             compact, dv_compact, count, cregs)

    def next_offset(self, addrsep: int) -> int:
        return self.offset + len(self.cregs) * addrsep

    def get_n_bits(self, bittype: List[str] = ["q"]) -> int:
        return sum(reg.get_n_bits(bittype) for reg in self.cregs)

    def get_field_list(self) -> List[Field]:
        ret = []
        for reg in self.cregs:
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
        attrs = [
            'async_name', 'async_clk', 'sync_name', 'sync_clk', 'count',
            'regwen_multi', 'compact'
        ]
        for attr in attrs:
            if getattr(self, attr) != getattr(alias_reg, attr):
                raise ValueError(
                    f'Value mismatch for attribute {attr} between alias '
                    f'multireg {self.name} and multireg {alias_reg.name} in '
                    f'{where}.')

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
        assert (len(self.cregs) == len(alias_reg.cregs))
        # Finally, iterate over expanded regs and update them as well.
        for creg, alias_creg in zip(self.cregs, alias_reg.cregs):
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
        for creg in self.cregs:
            creg.scrub_alias(where)
