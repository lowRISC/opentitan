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


class EmptyMultiRegException(Exception):
    '''A MultiRegister was requested without a positive count.'''
    def __init__(self, name: str, count: int):
        self.name = name
        self.count = count

    def __str__(self) -> str:
        return (f"Multireg {self.name} has a count of {self.count}, "
                "which isn't positive.")


class MultiRegister(RegBase):
    """One or more copies of an underlying register.

    Instance variables:

      pregs        The "pseudo-registers" that get represented by the
                   MultiRegister. These will be represented by concrete
                   registers in the design and each concrete register will
                   contain one or more pseudo-registers.

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

      needs_qe     This is true iff at least one of the pseudo-registers in the
                   multi-register needs a q-enable signal.
    """

    def __init__(self,
                 name: str,
                 offset: int,
                 alias_target: Optional[str],
                 pregs: List[Register],
                 cname: str,
                 regwen_multi: bool,
                 compact: bool,
                 dv_compact: bool,
                 cregs: List[Register]):

        # There should be at least one preg and creg. This will be checked in
        # the caller, so we can just assert it here.
        assert pregs
        assert cregs

        # This only makes sense if all the pseudo-registers are "compatible".
        # This means:
        #
        # - They should have the same associated clocks (async_name, async_clk,
        #   sync_name, sync_clk). We expect that to be checked in the caller
        #   (probably MultiRegister.from_raw), so can check it with just an
        #   assertion here.
        #
        # - They should either all have homogeneous fields or none of them
        #   should have them.
        #
        # While we iterate over the pseudo-registers, we can also compute
        # needs_qe.
        homogeneous = pregs[0].is_homogeneous()
        needs_qe = False
        for preg in pregs[1:]:
            assert preg.async_name == pregs[0].async_name
            assert preg.async_clk == pregs[0].async_clk
            assert preg.sync_name == pregs[0].sync_name
            assert preg.sync_clk == pregs[0].sync_clk
            assert preg.is_homogeneous() == homogeneous
            needs_qe |= preg.needs_qe()

        super().__init__(name, offset,
                         pregs[0].async_name, pregs[0].async_clk,
                         pregs[0].sync_name, pregs[0].sync_clk, alias_target)
        self.pregs = pregs
        self.cname = cname
        self.regwen_multi = regwen_multi
        self.compact = compact
        self.dv_compact = dv_compact
        self.cregs = cregs
        self._needs_qe = needs_qe

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

        name = check_name(rd['name'], 'name of multi-register')

        count_str = check_str(rd['count'], f'count field of multireg {name}')
        count = params.expand(count_str, f'count field of multireg {name}')

        if count <= 0:
            raise EmptyMultiRegException(name, count)

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

        # Parse the dictionary multiple times, passing in a value for
        # "multireg_idx". Collect up the resulting parsed pseudo-registers into
        # a pregs list.
        pregs = [Register.from_raw(reg_width, offset, params, reg_rd, clocks,
                                   is_alias, multireg_idx)
                 for multireg_idx in range(count)]

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

        # Check whether every preg has just one field, and compute the maximum
        # preg width. That maximum width only matters if single_field_per_preg
        # is True, so we just measure the first field each time.
        single_field_per_preg = True
        preg_max_width = 0
        for preg in pregs:
            preg_max_width = max(preg_max_width, preg.fields[0].bits.msb + 1)
            if len(preg.fields) != 1:
                single_field_per_preg = False
                break

        # Should the multi-register be compact? We expect it to be considered
        # compact if both of:
        #
        #  - Each pseudo-register has just one field.
        #
        #  - The regwen_multi flag is false. (If not, we need a different
        #    regwen and hence concrete register for each pseudo-register)
        #
        # The dictionary can override this to stop the multi-register being
        # compact even though these two properties are both true, but we check
        # in the other direction.

        default_compact = single_field_per_preg and not regwen_multi
        compact = check_bool(rd.get('compact', default_compact),
                             f'compact field of multireg {name}')

        if compact and not single_field_per_preg:
            raise ValueError(f'Multireg {name} sets the compact flag '
                             'but has multiple fields.')
        if compact and regwen_multi:
            raise ValueError(f'Multireg {name} sets the compact flag '
                             'but has regwen_multi set.')

        # The checks above should have checked that we cannot "turn on" being
        # compact with the config file. Make sure of this explictly.
        assert default_compact or not compact

        # Generate the registers that this multireg expands into. Here, a
        # "creg" is a "compacted register", which might contain multiple actual
        # registers.
        if compact:
            assert preg_max_width <= reg_width
            regs_per_creg = reg_width // preg_max_width
        else:
            regs_per_creg = 1

        cregs = []
        creg_count = (count + regs_per_creg - 1) // regs_per_creg
        for creg_idx in range(creg_count):
            min_reg_idx = regs_per_creg * creg_idx
            max_reg_idx = min(min_reg_idx + regs_per_creg, count) - 1
            creg_offset = offset + creg_idx * addrsep

            pregs_for_creg = [(pregs[i], i)
                              for i in range(min_reg_idx, max_reg_idx + 1)]
            preg0 = pregs_for_creg[0][0]

            creg_suff = f'_{creg_idx}' if creg_count > 1 else ''
            alias_target = (alias_target + creg_suff
                            if alias_target is not None else None)

            if regwen_multi and preg0.regwen is not None and creg_count > 1:
                merged_regwen = preg0.regwen + creg_suff  # type: Optional[str]
            else:
                merged_regwen = preg0.regwen

            field_desc_override = None
            strip_field = False
            if creg_idx > 0:
                field_desc_override = f'For {cname}{creg_idx}'
                strip_field = True

            creg = Register.collect_registers(creg_offset,
                                              preg0.name + creg_suff,
                                              pregs_for_creg,
                                              alias_target,
                                              merged_regwen,
                                              field_desc_override,
                                              strip_field)

            # Check that we haven't overflowed the register width. This
            # shouldn't happen (because of how we calculate regs_per_creg).
            assert creg.fields[-1].bits.msb < reg_width

            cregs.append(creg)

        # dv_compact is true if the multireg can be equally divided, and we can
        # pack them as an array
        dv_compact = (count < regs_per_creg or (count % regs_per_creg) == 0)

        return MultiRegister(name, offset, alias_target,
                             pregs, cname, regwen_multi,
                             compact, dv_compact, cregs)

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
        assert self.pregs
        return self.pregs[0].is_homogeneous()

    def needs_qe(self) -> bool:
        return self._needs_qe

    def _asdict(self) -> Dict[str, object]:
        # The _asdict method is essentially the inverse of from_raw, so we are
        # generating a dictionary that (when rendered in json) can be parsed as
        # this object again. The current representation is essentially one
        # register which should be replicated, and we use self.pregs0[0]: we
        # checked in our constructor that the other pregs will give compatible
        # representations.
        assert self.pregs
        rd = self.pregs[0]._asdict()
        rd['count'] = str(len(self.pregs))
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

        # Update each pseudo-register with the corresponding pseudo-register
        # from alias_reg.
        if len(alias_reg.pregs) != len(self.pregs):
            raise ValueError(f'Aliasing multireg has {len(alias_reg.pregs)} '
                             f'pseudo-registers but {self.name} only has '
                             f'{len(self.pregs)} in {where}.')
        for preg, alias_preg in zip(self.pregs, alias_reg.pregs):
            preg.apply_alias(alias_preg, where)

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

        #  Update each pseudo-register.
        for preg in self.pregs:
            preg.scrub_alias(where)

        # Finally, iterate over expanded regs and scrub them as well.
        for creg in self.cregs:
            creg.scrub_alias(where)
