# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, List, Optional, Tuple

from design.mubi import prim_mubi

from reggen.access import SWAccess, HWAccess
from reggen.clocking import Clocking, ClockingItem
from reggen.field import Field
from reggen.lib import (check_keys, check_str, check_name, check_bool,
                        check_list, check_str_list, check_int)
from reggen.params import ReggenParams
from reggen.reg_base import RegBase

import re

REQUIRED_FIELDS = {
    'name': ['s', "name of the register"],
    'desc': [
        't', "description of the register. "
        "This field supports the markdown syntax."
    ],
    'fields': ['l', "list of register field description groups"]
}

OPTIONAL_FIELDS = {
    'alias_target':
    ['s', "name of the register to apply the alias definition to."],
    'async': [
        's', "indicates the register must cross to a different "
        "clock domain before use.  The value shown here "
        "should correspond to one of the module's clocks."
    ],
    'sync': [
        's',
        "indicates the register needs to be on another clock/reset domain."
        "The value shown here should correspond to one of the module's clocks."
    ],
    'swaccess': [
        's', "software access permission to use for "
        "fields that don't specify swaccess"
    ],
    'hwaccess': [
        's', "hardware access permission to use for "
        "fields that don't specify hwaccess"
    ],
    'hwext': [
        's', "'true' if the register is stored outside "
        "of the register module"
    ],
    'hwqe': [
        's', "'true' if hardware uses 'q' enable signal, "
        "which is latched signal of software write pulse."
    ],
    'hwre': [
        's', "'true' if hardware uses 're' signal, "
        "which is latched signal of software read pulse."
    ],
    'regwen': [
        's', "if register is write-protected by another register, that "
        "register name should be given here. empty-string for no register "
        "write protection"
    ],
    'resval': ['d', "reset value of full register (default 0)"],
    'tags': [
        's',
        "tags for the register, following the format 'tag_name:item1:item2...'"
    ],
    'shadowed': ['s', "'true' if the register is shadowed"],
    'update_err_alert': [
        's', "alert that will be triggered if "
        "this shadowed register has update error"
    ],
    'storage_err_alert': [
        's', "alert that will be triggered if "
        "this shadowed register has storage error"
    ],
    'writes_ignore_errors': [
        'b',
        "This register may update on a TL write that causes an error response."
    ]
}


class Register(RegBase):
    '''Code representing a register for reggen'''
    def __init__(self,
                 offset: int,
                 name: str,
                 alias_target: Optional[str],
                 desc: str,
                 async_name: Optional[str],
                 async_clk: Optional[ClockingItem],
                 sync_name: Optional[str],
                 sync_clk: Optional[ClockingItem],
                 hwext: bool,
                 hwqe: bool,
                 hwre: bool,
                 regwen: Optional[str],
                 tags: List[str],
                 resval: Optional[int],
                 shadowed: bool,
                 fields: List[Field],
                 update_err_alert: Optional[str],
                 storage_err_alert: Optional[str],
                 writes_ignore_errors: bool):
        super().__init__(name, offset,
                         async_name, async_clk, sync_name, sync_clk,
                         alias_target)
        self.desc = desc
        self.hwext = hwext
        self.hwqe = hwqe
        self.hwre = hwre
        if self.hwre and not self.hwext:
            raise ValueError(
                f'The {self.name} register specifies hwre but not hwext.')

        self.regwen = regwen
        self.tags = tags

        self.shadowed = shadowed
        pattern = r'^[a-z0-9_]+_shadowed(?:_[0-9]+)?'
        sounds_shadowy = re.match(pattern, self.name.lower())
        if self.shadowed and not sounds_shadowy:
            raise ValueError(
                f"Register {self.name} has the shadowed flag but its name "
                "doesn't end with the _shadowed suffix.")
        elif sounds_shadowy and not self.shadowed:
            raise ValueError(
                f"Register {self.name} has a name ending in _shadowed, but "
                "the shadowed flag is not set.")

        # Take a copy of fields and then sort by bit index
        assert fields
        self.fields = fields.copy()
        self.fields.sort(key=lambda field: field.bits.lsb)

        # Index fields by name and check for duplicates
        self.name_to_field = {}  # type: Dict[str, Field]
        for field in self.fields:
            if field.name in self.name_to_field:
                raise ValueError(
                    f'Register {self.name} has duplicate fields called '
                    f'{field.name}.')
            self.name_to_field[field.name] = field

        # Check that fields have compatible access types if we are hwext
        if self.hwext:
            for field in self.fields:
                if field.hwaccess.key == 'hro' and field.sw_readable():
                    raise ValueError(
                        f'The {self.name} register has hwext set, but field '
                        f'{field.name} has hro hwaccess and the field value '
                        'is readable by software (mode '
                        f'{field.swaccess.key}).')
                if not field.hwqe and field.sw_writable():
                    raise ValueError(
                        f'The {self.name} register has hwext set and field '
                        f'{field.name} is writable by software (mode '
                        f'{field.swaccess.key}), so the register must also '
                        'enable hwqe.')

        # Shadow registers do not support all swaccess types, hence we
        # need to check that here.
        if self.shadowed:
            for field in self.fields:
                if field.swaccess.key not in [
                        'rw', 'ro', 'wo', 'rw1s', 'rw0c'
                ]:
                    raise ValueError(
                        f"Shadowed register {self.name} has a field "
                        f"({field.name}) with incompatible type "
                        f"'{field.swaccess.key}'.")

        # Check that fields will be updated together. This generally comes "for
        # free", but there's a slight wrinkle with RC fields: these use the
        # register's read-enable input as their write-enable. We want to ensure
        # either that every field that is updated as a result of bus accesses
        # is RC or that none of them are.
        rc_fields = []
        we_fields = []
        for field in self.fields:
            if field.swaccess.key == 'rc':
                rc_fields.append(field.name)
            elif field.swaccess.allows_write():
                we_fields.append(field.name)
        if rc_fields and we_fields:
            raise ValueError(
                f"Register {self.name} has both software writable fields "
                f"({', '.join(rc_fields)}) and read-clear fields "
                f"({', '.join(we_fields)}), meaning it doesn't have a single "
                "write-enable signal.")

        # Check that field bits are disjoint
        bits_used = 0
        for field in self.fields:
            field_mask = field.bits.bitmask()
            if bits_used & field_mask:
                raise ValueError(
                    f'Register {self.name} has non-disjoint fields: '
                    f'{field.name} uses bits {bits_used & field_mask:#x} '
                    'used by other fields.')

        # Compute a reset value and mask from our constituent fields.
        self.resval = 0
        self.resmask = 0
        for field in self.fields:
            self.resval |= (field.resval or 0) << field.bits.lsb
            self.resmask |= field.bits.bitmask()

        # If the register defined a reset value, make sure it matches. We've
        # already checked that each field matches, but we still need to make
        # sure there weren't any bits unaccounted for.
        if resval is not None and self.resval != resval:
            raise ValueError(
                f'Register {self.name} specifies a reset value of '
                f'{resval:#x} but collecting reset values across its fields '
                f'yields {self.resval:#x}.')

        self.update_err_alert = update_err_alert
        self.storage_err_alert = storage_err_alert

        self.writes_ignore_errors = writes_ignore_errors

    @staticmethod
    def from_raw(reg_width: int,
                 offset: int,
                 params: ReggenParams,
                 raw: object,
                 clocks: Clocking,
                 is_alias: bool,
                 multireg_idx: Optional[int]) -> 'Register':
        rd = check_keys(raw, 'register', list(REQUIRED_FIELDS.keys()),
                        list(OPTIONAL_FIELDS.keys()))

        name = check_name(rd['name'], 'name of register')

        alias_target = None
        if rd.get('alias_target') is not None:
            if is_alias:
                alias_target = check_name(rd['alias_target'],
                                          'name of alias target register')
            else:
                raise ValueError(
                    f'Field {name} may not have an alias_target key')
        elif is_alias:
            raise ValueError(f'alias register {name} does not define the '
                             'alias_target key.')

        # If multireg_idx is not None then we are parsing a pseudo-register for
        # some multi-register. Set up the bindings that we pass to
        # Field.from_raw to reflect that.
        field_bindings = {}
        if multireg_idx is not None:
            field_bindings['multireg_idx'] = multireg_idx

        desc = check_str(rd['desc'], f'desc for {name} register')

        async_name = None  # type: Optional[str]
        async_clk = None  # type: Optional[ClockingItem]

        async_obj = rd.get('async')
        if async_obj is not None:
            async_name = check_str(async_obj,
                                   f'async clock for {name} register')
            valid_clocks = clocks.clock_signals()
            if async_name not in valid_clocks:
                raise ValueError(
                    f'async clock {async_name} defined for {name} does not '
                    f'exist in valid module clocks {valid_clocks}.')
            else:
                async_clk = clocks.get_by_clock(async_name)

        sync_name = None  # type: Optional[str]
        sync_clk = None  # type: Optional[ClockingItem]

        sync_obj = rd.get('sync')
        if sync_obj is not None:
            sync_name = check_str(sync_obj,
                                  f'different sync clock for {name} register')
            valid_clocks = clocks.clock_signals()
            if sync_name not in valid_clocks:
                raise ValueError(
                    f'sync clock {sync_name} defined for {name} does not '
                    f'exist in valid module clocks {valid_clocks}.')
            else:
                sync_clk = clocks.get_by_clock(sync_name)

        swaccess = SWAccess(f'{name} register', rd.get('swaccess', 'none'))
        hwaccess = HWAccess(f'{name} register', rd.get('hwaccess', 'hro'))

        hwext = check_bool(rd.get('hwext', False),
                           f'hwext flag for {name} register')

        hwqe = check_bool(rd.get('hwqe', False),
                          f'hwqe flag for {name} register')

        hwre = check_bool(rd.get('hwre', False),
                          f'hwre flag for {name} register')

        raw_regwen = rd.get('regwen', '')
        if not raw_regwen:
            regwen = None
        else:
            regwen = check_name(raw_regwen, f'regwen for {name} register')

        raw_resval = rd.get('resval')
        if raw_resval is None:
            resval = None
        else:
            resval = check_int(raw_resval, f'resval for {name} register')
            if not 0 <= resval < (1 << reg_width):
                raise ValueError(f'resval for {name} register is {resval}, '
                                 f'not an unsigned {reg_width}-bit number.')

        tags = check_str_list(rd.get('tags', []), f'tags for {name} register')

        shadowed = check_bool(rd.get('shadowed', False),
                              f'shadowed flag for {name} register')

        raw_fields = check_list(rd['fields'], f'fields for {name} register')
        if not raw_fields:
            raise ValueError(f'Register {name} has no fields.'.format(name))

        fields = []
        used_bits = 0
        for idx, rf in enumerate(raw_fields):

            field = (Field.from_raw(name,
                                    idx,
                                    len(raw_fields),
                                    swaccess,
                                    hwaccess,
                                    resval,
                                    reg_width,
                                    params,
                                    hwext,
                                    hwqe,
                                    shadowed,
                                    is_alias,
                                    rf,
                                    field_bindings))

            overlap_bits = used_bits & field.bits.bitmask()
            if overlap_bits:
                raise ValueError(f'Field {field.name} uses bits '
                                 f'{overlap_bits:#x} that appear in other '
                                 f'fields.')

            used_bits |= field.bits.bitmask()
            fields.append(field)

        raw_uea = rd.get('update_err_alert')
        if raw_uea is None:
            update_err_alert = None
        else:
            update_err_alert = check_name(
                raw_uea, f'update_err_alert for {name} register')

        raw_sea = rd.get('storage_err_alert')
        if raw_sea is None:
            storage_err_alert = None
        else:
            storage_err_alert = check_name(
                raw_sea, f'storage_err_alert for {name} register')

        writes_ignore_errors = \
            check_bool(rd.get('writes_ignore_errors', False),
                       'writes_ignore_errors flag for {} register'
                       .format(name))

        return Register(offset, name, alias_target, desc, async_name,
                        async_clk, sync_name, sync_clk, hwext, hwqe, hwre,
                        regwen, tags, resval, shadowed, fields,
                        update_err_alert, storage_err_alert,
                        writes_ignore_errors)

    def next_offset(self, addrsep: int) -> int:
        return self.offset + addrsep

    def get_n_bits(self, bittype: List[str]) -> int:
        return sum(
            field.get_n_bits(self.hwext, self.hwre, bittype)
            for field in self.fields)

    def get_field_list(self) -> List[Field]:
        return self.fields

    def is_homogeneous(self) -> bool:
        return len(self.fields) == 1

    def is_hw_writable(self) -> bool:
        '''Returns true if any field in this register can be modified by HW'''
        for fld in self.fields:
            if fld.hwaccess.allows_write():
                return True
        return False

    def get_width(self) -> int:
        '''Get the width of the fields in the register in bits

        This counts dead space between and below fields, so it's calculated as
        one more than the highest msb.

        '''
        # self.fields is ordered by (increasing) LSB, so we can find the MSB of
        # the register by taking the MSB of the last field.
        return 1 + self.fields[-1].bits.msb

    def needs_we(self) -> bool:
        '''Return true if at least one field needs a write-enable'''
        for fld in self.fields:
            if fld.swaccess.needs_we():
                return True
        return False

    def needs_qe(self) -> bool:
        '''Return true if the register or at least one field needs a q-enable'''
        if self.hwqe:
            return True
        for fld in self.fields:
            if fld.hwqe:
                return True
        return False

    def needs_int_qe(self) -> bool:
        '''Return true if the register or at least one field needs an
           internal q-enable.  An internal q-enable means the net
           may be consumed by other reg logic but will not be exposed
           in the package file.'''
        if self.async_clk and self.is_hw_writable():
            return True
        else:
            return self.needs_qe()

    def needs_re(self) -> bool:
        '''Return true if at least one field needs a read-enable

        This is true if any of the following are true:

          - The register is shadowed, because the read has a side effect.
            I.e., this puts the register back into Phase 0 (next write will
            go to the staged register). This is useful for software in case
            it lost track of the current phase. See comportability spec for
            more details:
            https://docs.opentitan.org/doc/rm/register_tool/#shadow-registers

          - There's an RC field (where we'll attach the read-enable signal to
            the subreg's we port)

          - The register is hwext and allows reads (in which case the hardware
            side might need the re signal)

        '''
        if self.shadowed:
            return True

        for fld in self.fields:
            if fld.swaccess.key == 'rc':
                return True

            if self.hwext and fld.swaccess.allows_read():
                return True

        return False

    @staticmethod
    def collect_registers(offset: int,
                          name: str,
                          regs: List[Tuple['Register', int]],
                          alias_target: Optional[str],
                          regwen: Optional[str],
                          field_desc_override: Optional[str],
                          strip_field: bool) -> 'Register':
        '''Create a register that holds the fields from regs.

        The merged register will be have address offset and be called name.

        The regs argument should be a list of pairs (reg, idx) which means that
        we want a copy of reg, but renamed by appending "_<idx>". These input
        registers are concatenated, including gaps before field LSBs.

        If alias_target is not None, the merged register will be an alias
        register that points at the named register.

        If regwen is not None, this names a regwen register that should be used
        by the merged register. We check ensures that it has a non-None value
        if any element of regs has a regwen.

        If field_desc_override is not None, it will be used instead of fields' desc
        values.

        If strip_field is True, we drop any values from field enum types.
        '''
        assert regs

        fields = []
        bit_idx = 0

        reg0 = regs[0][0]

        # Check that the registers can be collected together (because they have
        # compatible values for other instance variables). This is done with
        # "assert" because if it fails then this is probably a programming
        # error in reggen.
        for reg, _ in regs[1:]:
            assert reg.desc == reg0.desc
            assert reg.async_name == reg0.async_name
            assert reg.async_clk == reg0.async_clk
            assert reg.sync_name == reg0.sync_name
            assert reg.sync_clk == reg0.sync_clk
            assert reg.hwext == reg0.hwext
            assert reg.hwqe == reg0.hwqe
            assert reg.hwre == reg0.hwre
            assert reg.tags == reg0.tags
            assert reg.shadowed == reg0.shadowed
            assert reg.update_err_alert == reg0.update_err_alert
            assert reg.storage_err_alert == reg0.storage_err_alert
            assert reg.writes_ignore_errors == reg0.writes_ignore_errors

        for reg, reg_idx in regs:
            assert reg.regwen is None or regwen is not None

            # We want to collect up all the fields from this input register,
            # starting with an LSB of bit_idx
            reg_bit0 = bit_idx
            bit_idx += reg.fields[-1].bits.msb + 1

            for field in reg.fields:
                field_name_suff = f'_{reg_idx}'

                # Translate the field to match the copy of the register that
                # started at reg_bit0
                field_copy = field.make_translated(reg_bit0)

                # The generated field will need a name based on reg_idx (the
                # index of the register copy that's being used). Similarly, we
                # have to redirect any alias_target if there is one.
                field_copy.name += field_name_suff
                if field_copy.alias_target is not None:
                    field_copy.alias_target += field_name_suff

                # Apply field_desc_override (which allows the caller to
                # simplify documentation for the field when there are lots of
                # copies).
                if field_desc_override is not None:
                    field_copy.desc = field_desc_override

                # Finally, strip out any associated enum type if that was
                # requested.
                if strip_field:
                    field_copy.enum = None

                fields.append(field_copy)

        # Don't specify a reset value for the new register. Any reset value
        # defined for the original register will have propagated to its fields,
        # so when we combine them here, the Register constructor can compute a
        # reset value for us (which might well be different from self.resval if
        # we've replicated fields).
        new_resval = None

        return Register(offset, name, alias_target, reg0.desc,
                        reg0.async_name, reg0.async_clk,
                        reg0.sync_name, reg0.sync_clk,
                        reg0.hwext, reg0.hwqe, reg0.hwre, regwen,
                        reg0.tags, new_resval, reg0.shadowed, fields,
                        reg0.update_err_alert, reg0.storage_err_alert,
                        reg0.writes_ignore_errors)

    def check_valid_regwen(self) -> None:
        '''Check that this register is valid for use as a REGWEN'''
        # Async REGWEN registers are currently not supported.
        # The register write enable gating is always resolved on the
        # bus side.
        if self.async_clk is not None:
            raise ValueError(
                f'Regwen {self.name} cannot be declared as async.')

        # A REGWEN register should have a single field that's just bit zero.
        if len(self.fields) != 1:
            raise ValueError(
                f'One or more registers use {self.name} as a write-enable so '
                'it should have exactly one field. It actually has '
                f'{len(self.fields)}.')

        wen_fld = self.fields[0]
        if wen_fld.mubi:
            if wen_fld.bits.width() % 4:
                raise ValueError(
                    f'One or more registers use {self.name} as a multi-bit '
                    'write-enable so its field bit-width should be a multiple '
                    f'of 4, not {wen_fld.bits.width()}.')
        else:
            if wen_fld.bits.width() != 1:
                raise ValueError(
                    f'One or more registers use {self.name} as a write-enable '
                    'so its field should be 1 bit wide, not '
                    f'{wen_fld.bits.width()}.')
        if wen_fld.bits.lsb != 0:
            raise ValueError(
                f'One or more registers use {self.name} as a write-enable so '
                f'its field should have LSB 0, not {wen_fld.bits.lsb}.')

        # If the REGWEN bit is SW controlled, check that the register
        # defaults to enabled, which means 1 for single-bit REGWEN signals or
        # prim_mubi.mubi_value_as_int(True, 4) for 4-bit multi-bit REGWEN signals.
        # If this bit is read-only by SW and hence hardware controlled, we do not
        # enforce this requirement.
        if wen_fld.swaccess.key != "ro":
            if wen_fld.mubi:
                if self.resval != prim_mubi.mubi_value_as_int(
                        True, wen_fld.bits.width()):
                    raise ValueError(
                        f'One or more registers use {self.name} as a '
                        'multi-bit write-enable. Since it is SW-controlled '
                        'it should have a multi-bit TRUE reset value.')
            else:
                if not self.resval:
                    raise ValueError(
                        f'One or more registers use {self.name} as a '
                        'write-enable. Since it is SW-controlled it should '
                        'have a nonzero reset value.')

        if wen_fld.swaccess.key == "rw0c":
            # The register is software managed: all good!
            return

        if wen_fld.swaccess.key == "ro" and wen_fld.hwaccess.key == "hwo":
            # The register is hardware managed: that's fine too.
            return

        raise ValueError(
            f'One or more registers use {self.name} as a write-enable. '
            'However, its field has invalid access permissions '
            f'({wen_fld.swaccess.key} / {wen_fld.hwaccess.key}). It should '
            'either have swaccess=RW0C or have swaccess=RO and hwaccess=HWO.')

    def bitmask(self) -> str:
        reg_bitmask = 0
        for f in self.fields:
            reg_bitmask |= f.bits.bitmask()

        return format(reg_bitmask, "x")

    def _asdict(self) -> Dict[str, object]:
        rd = {
            'name': self.name,
            'desc': self.desc,
            'fields': self.fields,
            'hwext': str(self.hwext),
            'hwqe': str(self.hwqe),
            'hwre': str(self.hwre),
            'tags': self.tags,
            'shadowed': str(self.shadowed),
        }  # type: Dict[str, object]
        if self.regwen is not None:
            rd['regwen'] = self.regwen
        if self.update_err_alert is not None:
            rd['update_err_alert'] = self.update_err_alert
        if self.storage_err_alert is not None:
            rd['storage_err_alert'] = self.storage_err_alert
        if self.alias_target is not None:
            rd['alias_target'] = self.alias_target

        return rd

    def apply_alias(self, alias_reg: 'Register', where: str) -> None:
        '''Compare all attributes and replace overridable values.

        This updates the overridable register and field attributes with the
        alias values and ensures that all non-overridable attributes have
        identical values.
        '''
        # Attributes to be crosschecked
        attrs = [
            'async_name', 'async_clk', 'hwext', 'hwqe', 'hwre',
            'update_err_alert', 'storage_err_alert', 'shadowed'
        ]
        for attr in attrs:
            if getattr(self, attr) != getattr(alias_reg, attr):
                raise ValueError(
                    'Value mismatch for attribute {attr} between alias '
                    f'register {self.name} and register {alias_reg.name} in '
                    f'{where}.')

        # These attributes can be overridden by the aliasing mechanism.
        self.name = alias_reg.name
        self.desc = alias_reg.desc
        self.resval = alias_reg.resval
        self.tags = alias_reg.tags
        self.regwen = alias_reg.regwen

        # We also keep track of the alias_target when overriding attributes.
        # This gives us a way to check whether a register has been overridden
        # or not, and what the name of the original register was.
        self.alias_target = alias_reg.alias_target

        # Update the fields.
        if len(alias_reg.fields) != len(self.fields):
            raise ValueError(
                'The number of fields does not match for alias register '
                f'{alias_reg.name} and register {self.name} in {where}.')

        fields = zip(alias_reg.fields, self.fields)
        for k, (alias_field, field) in enumerate(fields):
            # Infer the aliased field name if it has not been defined.
            if alias_field.alias_target is None:
                alias_field.alias_target = field.name
            # Otherwise the names need to match
            elif alias_field.alias_target != field.name:
                raise ValueError(
                    'Inconsistent aliased field name '
                    f'{alias_field.alias_target} in alias register '
                    f'{alias_reg.alias_target} in {where}.')

            # Validate and override attributes.
            field.apply_alias(alias_field, where)

    def scrub_alias(self, where: str) -> None:
        '''Replaces sensitive fields in register with generic names

        This function can be used to create the generic register descriptions
        from full alias hjson definitions. It will only work on registers
        where the alias_target keys are defined, and otherwise throw an error.
        '''
        # These attributes are scrubbed
        assert self.alias_target is not None
        self.name = self.alias_target
        self.desc = ''
        self.resval = 0
        self.tags = []
        self.alias_target = None

        # First check that custom alias_target names are unique and that
        # the numbering is correct if the name is of the form field[0-9]+.
        known_field_names = {}
        for k, field in enumerate(self.fields):
            if field.alias_target is not None:
                m = re.match(r'field[0-9]+', field.alias_target)
                if m and field.alias_target != f'field{k}':
                    raise ValueError(
                        f'Alias field alias_target {field.alias_target} is '
                        f'incorrectly numbered in alias register {self.name} '
                        f'in {where}.')
                elif field.alias_target in known_field_names:
                    raise ValueError(
                        f'Alias field alias_target {field.alias_target} is '
                        f'not unique in alias register {self.name} in '
                        f'{where}.')
                else:
                    known_field_names.update({field.alias_target: 1})

        # Then, assign the field names
        for k, field in enumerate(self.fields):
            if field.alias_target is not None:
                field.name = field.alias_target
                field.alias_target = None
            # Infer the aliased field name if it has not been defined.
            else:
                field.name = f'field{k}'

            # Scrub field contents.
            field.scrub_alias(where)
