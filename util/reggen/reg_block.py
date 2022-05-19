# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing the registers, windows etc. for a block'''

import re
from typing import Callable, Dict, List, Optional, Sequence, Union

from .alert import Alert
from .access import SWAccess, HWAccess
from .bus_interfaces import BusInterfaces
from .clocking import Clocking, ClockingItem
from .field import Field
from .signal import Signal
from .lib import check_int, check_list, check_str_dict, check_str
from .multi_register import MultiRegister
from .params import ReggenParams
from .register import Register
from .window import Window


class RegBlock:
    def __init__(self, reg_width: int, params: ReggenParams):

        self._addrsep = (reg_width + 7) // 8
        self._reg_width = reg_width
        self._params = params

        self.name = ""  # type: str
        self.clocks = {}  # type: Dict[str, ClockingItem]
        self.offset = 0
        self.multiregs = []  # type: List[MultiRegister]
        self.registers = []  # type: List[Register]
        self.windows = []  # type: List[Window]

        # Boolean indication whether ANY window in regblock has data integrity passthrough
        self.has_data_intg_passthru = False

        # A list of all registers, expanding multiregs, ordered by offset
        self.flat_regs = []  # type: List[Register]

        # A list of registers and multiregisters (unexpanded)
        self.all_regs = []  # type: List[Union[Register, MultiRegister]]

        # A list of all the underlying register types used in the block. This
        # has one entry for each actual Register, plus a single entry giving
        # the underlying register for each MultiRegister.
        self.type_regs = []  # type: List[Register]

        # A list with everything in order
        self.entries = []  # type: List[object]

        # A dict of named entries, mapping name to offset
        self.name_to_offset = {}  # type: Dict[str, int]

        # A dict of all registers (expanding multiregs), mapping name to the
        # register object
        self.name_to_flat_reg = {}  # type: Dict[str, Register]

        # A list of all write enable names
        self.wennames = []  # type: List[str]

        # Boolean indication that the block is fully asynchronous
        self.async_if = False

    @staticmethod
    def build_blocks(block: 'RegBlock',
                     raw: object,
                     bus: BusInterfaces,
                     clocks: Clocking) -> Dict[Optional[str], 'RegBlock']:
        '''Build a dictionary of blocks for a 'registers' field in the hjson

        There are two different syntaxes we might see here. The simple syntax
        just consists of a list of entries (register, multireg, window,
        skipto). If we see that, each entry gets added to init_block and then
        we return {None: init_block}.

        The more complicated syntax is a dictionary. This parses from hjson as
        an OrderedDict which we walk in document order. Entries from the first
        key/value pair in the dictionary will be added to init_block. Later
        key/value pairs start empty RegBlocks. The return value is a dictionary
        mapping the keys we saw to their respective RegBlocks.

        '''
        if isinstance(raw, list):
            # This is the simple syntax
            block.add_raw_registers(raw,
                                    'registers field at top-level',
                                    clocks,
                                    bus.device_async.get(None))
            return {None: block}

        # This is the more complicated syntax
        if not isinstance(raw, dict):
            raise ValueError('registers field at top-level is '
                             'neither a list or a dictionary.')

        ret = {}  # type: Dict[Optional[str], RegBlock]
        for idx, (r_key, r_val) in enumerate(raw.items()):
            if idx > 0:
                block = RegBlock(block._reg_width, block._params)

            rb_key = check_str(r_key,
                               'the key for item {} of '
                               'the registers dictionary at top-level'
                               .format(idx + 1))
            rb_val = check_list(r_val,
                                'the value for item {} of '
                                'the registers dictionary at top-level'
                                .format(idx + 1))

            block.add_raw_registers(rb_val,
                                    'item {} of the registers '
                                    'dictionary at top-level'
                                    .format(idx + 1),
                                    clocks,
                                    bus.device_async.get(r_key))
            block.validate()

            assert rb_key not in ret
            block.name = rb_key
            ret[rb_key] = block

        return ret

    def add_raw_registers(self,
                          raw: object,
                          what: str,
                          clocks: Clocking,
                          async_if: Optional[str]) -> None:

        # the interface is fully asynchronous
        if async_if:
            self.async_if = True
            self.clocks[async_if] = clocks.get_by_clock(async_if)

        rl = check_list(raw, 'registers field at top-level')
        for entry_idx, entry_raw in enumerate(rl):
            where = ('entry {} of the top-level registers field'
                     .format(entry_idx + 1))
            self.add_raw(where, entry_raw, clocks)

    def add_raw(self,
                where: str,
                raw: object,
                clocks: Clocking) -> None:
        entry = check_str_dict(raw, where)

        handlers = {
            'register': self._handle_register,
            'reserved': self._handle_reserved,
            'skipto': self._handle_skipto,
            'window': self._handle_window,
            'multireg': self._handle_multireg
        }

        entry_type = 'register'
        entry_body = entry  # type: object

        for t in ['reserved', 'skipto', 'window', 'multireg']:
            t_body = entry.get(t)
            if t_body is not None:
                # Special entries look like { window: { ... } }, so if we
                # get a hit, this should be the only key in entry. Note
                # that this also checks that nothing has more than one
                # entry type.
                if len(entry) != 1:
                    other_keys = [k for k in entry if k != t]
                    assert other_keys
                    raise ValueError('At offset {:#x}, {} has key {}, which '
                                     'should give its type. But it also has '
                                     'other keys too: {}.'
                                     .format(self.offset,
                                             where, t, ', '.join(other_keys)))
                entry_type = t
                entry_body = t_body

        entry_where = ('At offset {:#x}, {}, type {!r}'
                       .format(self.offset, where, entry_type))

        handlers[entry_type](entry_where, entry_body, clocks)

    def _validate_async(self, name: Optional[str], clk: object) -> None:
        '''Check for async definition consistency

        If a reg block is marked fully asynchronous through its bus interface,
        its register definition cannot also mark individual registers with
        asynchronous designations.

        The two asynchronous regfile schemes are mutually exclusive.
        '''

        if self.name:
            block_name = self.name
        else:
            block_name = "Default"

        if self.async_if and name:
            raise ValueError(f'''
            {block_name} register block has incompatible async definitions.
            The corresponding device interface is marked fully async, however
            there are individual registers that also contain the async_clk
            designation, this is not allowed.

            Either remove all register async_clk designations, or remove
            async designation of the bus interface.
            ''')

        # If there is an asynchronous clock defined, then the clock must be a
        # valid clocking item
        if name:
            assert isinstance(clk, ClockingItem)
            self.clocks[name] = clk

    def _handle_register(self, where: str, body: object, clocks: Clocking) -> None:
        reg = Register.from_raw(self._reg_width,
                                self.offset, self._params, body, clocks)

        self._validate_async(reg.async_name, reg.async_clk)

        self.add_register(reg)

    def _handle_reserved(self, where: str, body: object, clocks: Optional[Clocking]) -> None:
        nreserved = check_int(body, 'body of ' + where)
        if nreserved <= 0:
            raise ValueError('Reserved count in {} is {}, '
                             'which is not positive.'
                             .format(where, nreserved))

        self.offset += self._addrsep * nreserved

    def _handle_skipto(self, where: str, body: object, clocks: Optional[Clocking]) -> None:
        skipto = check_int(body, 'body of ' + where)
        if skipto < self.offset:
            raise ValueError('Destination of skipto in {} is {:#x}, '
                             'is less than the current offset, {:#x}.'
                             .format(where, skipto, self.offset))
        if skipto % self._addrsep:
            raise ValueError('Destination of skipto in {} is {:#x}, '
                             'not a multiple of addrsep, {:#x}.'
                             .format(where, skipto, self._addrsep))
        self.offset = skipto

    def _handle_window(self, where: str, body: object, clocks: Optional[Clocking]) -> None:
        window = Window.from_raw(self.offset,
                                 self._reg_width, self._params, body)
        if window.name is not None:
            lname = window.name.lower()
            if lname in self.name_to_offset:
                raise ValueError('Window {} (at offset {:#x}) has the '
                                 'same name as something at offset {:#x}.'
                                 .format(window.name, window.offset,
                                         self.name_to_offset[lname]))
        self.add_window(window)

    def _handle_multireg(self, where: str, body: object, clocks: Clocking) -> None:
        mr = MultiRegister(self.offset,
                           self._addrsep, self._reg_width, self._params, body,
                           clocks)

        # validate async schemes
        self._validate_async(mr.async_name, mr.async_clk)

        for reg in mr.regs:
            lname = reg.name.lower()
            if lname in self.name_to_offset:
                raise ValueError('Multiregister {} (at offset {:#x}) expands '
                                 'to a register with name {} (at offset '
                                 '{:#x}), but this already names something at '
                                 'offset {:#x}.'
                                 .format(mr.reg.name, mr.reg.offset,
                                         reg.name, reg.offset,
                                         self.name_to_offset[lname]))
            self._add_flat_reg(reg)
            if mr.dv_compact is False:
                self.type_regs.append(reg)

        self.multiregs.append(mr)
        self.all_regs.append(mr)
        if mr.dv_compact is True:
            self.type_regs.append(mr.reg)
        self.entries.append(mr)
        self.offset = mr.next_offset(self._addrsep)

    def add_register(self, reg: Register) -> None:
        assert reg.offset == self.offset

        lname = reg.name.lower()
        if lname in self.name_to_offset:
            raise ValueError('Register {} (at offset {:#x}) has the same '
                             'name as something at offset {:#x}.'
                             .format(reg.name, reg.offset,
                                     self.name_to_offset[lname]))
        self._add_flat_reg(reg)

        self.registers.append(reg)
        self.all_regs.append(reg)
        self.type_regs.append(reg)
        self.entries.append(reg)
        self.offset = reg.next_offset(self._addrsep)

        if reg.regwen is not None and reg.regwen not in self.wennames:
            self.wennames.append(reg.regwen)

    def _add_flat_reg(self, reg: Register) -> None:
        lname = reg.name.lower()
        # The first assertion is checked at the call site (where we can print
        # out a nicer message for multiregs). The second assertion should be
        # implied by the first.
        assert lname not in self.name_to_offset
        assert lname not in self.name_to_flat_reg

        self.flat_regs.append(reg)
        self.name_to_flat_reg[lname] = reg
        self.name_to_offset[lname] = reg.offset

    def add_window(self, window: Window) -> None:
        if window.name is not None:
            lname = window.name.lower()
            assert lname not in self.name_to_offset
            self.name_to_offset[lname] = window.offset

        self.windows.append(window)
        self.entries.append(window)
        assert self.offset <= window.offset
        self.offset = window.next_offset(self._addrsep)

        self.has_data_intg_passthru |= window.data_intg_passthru

    def validate(self) -> None:
        '''Run this to check consistency after all registers have been added'''

        # Check that every write-enable register has a good name, a valid reset
        # value, and valid access permissions.
        for wenname in self.wennames:
            # check the REGWEN naming convention
            if re.fullmatch(r'(.+_)*REGWEN(_[0-9]+)?', wenname) is None:
                raise ValueError("Regwen name {} must have the suffix '_REGWEN'"
                                 .format(wenname))

            wen_reg = self.name_to_flat_reg.get(wenname.lower())
            if wen_reg is None:
                raise ValueError('One or more registers use {} as a '
                                 'write-enable, but there is no such register.'
                                 .format(wenname))

            wen_reg.check_valid_regwen()

    def get_n_bits(self, bittype: List[str] = ["q"]) -> int:
        '''Returns number of bits in registers in this block.

        This includes those expanded from multiregs. See Field.get_n_bits for a
        description of the bittype argument.

        '''
        return sum(reg.get_n_bits(bittype) for reg in self.flat_regs)

    def as_dicts(self) -> List[object]:
        entries = []  # type: List[object]
        offset = 0
        for entry in self.entries:
            assert (isinstance(entry, Register) or
                    isinstance(entry, MultiRegister) or
                    isinstance(entry, Window))

            next_off = entry.offset
            assert offset <= next_off
            res_bytes = next_off - offset
            if res_bytes:
                assert res_bytes % self._addrsep == 0
                entries.append({'reserved': res_bytes // self._addrsep})

            entries.append(entry)
            offset = entry.next_offset(self._addrsep)

        return entries

    _FieldFormatter = Callable[[bool, str], str]

    def _add_intr_alert_reg(self,
                            signals: Sequence[Signal],
                            reg_name: str,
                            reg_desc: str,
                            field_desc_fmt: Optional[Union[str, _FieldFormatter]],
                            swaccess: str,
                            hwaccess: str,
                            is_testreg: bool,
                            reg_tags: List[str]) -> None:
        swaccess_obj = SWAccess('RegBlock._make_intr_alert_reg()', swaccess)
        hwaccess_obj = HWAccess('RegBlock._make_intr_alert_reg()', hwaccess)

        fields = []
        for signal in signals:
            if field_desc_fmt is None:
                field_desc = signal.desc
            elif isinstance(field_desc_fmt, str):
                field_desc = field_desc_fmt
            else:
                width = signal.bits.width()
                field_desc = field_desc_fmt(width > 1, signal.name)

            fields.append(Field(signal.name,
                                field_desc or signal.desc,
                                tags=[],
                                swaccess=swaccess_obj,
                                hwaccess=hwaccess_obj,
                                hwqe=is_testreg,
                                bits=signal.bits,
                                resval=0,
                                enum=None,
                                mubi=False))

        reg = Register(self.offset,
                       reg_name,
                       reg_desc,
                       async_name="",
                       async_clk=None,
                       hwext=is_testreg,
                       hwqe=is_testreg,
                       hwre=False,
                       regwen=None,
                       tags=reg_tags,
                       resval=None,
                       shadowed=False,
                       fields=fields,
                       update_err_alert=None,
                       storage_err_alert=None)
        self.add_register(reg)

    def make_intr_regs(self, interrupts: Sequence[Signal]) -> None:
        assert interrupts
        assert interrupts[-1].bits.msb < self._reg_width

        self._add_intr_alert_reg(interrupts,
                                 'INTR_STATE',
                                 'Interrupt State Register',
                                 None,
                                 'rw1c',
                                 'hrw',
                                 False,
                                 # Some POR routines have the potential to
                                 # unpredictably set some `intr_state` fields
                                 # for various IPs, so we exclude all
                                 # `intr_state` accesses from CSR checks to
                                 # prevent this from occurring.
                                 #
                                 # An example of an `intr_state` mismatch error
                                 # occurring due to a POR routine can be seen in
                                 # issue #6888.
                                 ["excl:CsrAllTests:CsrExclAll"])
        self._add_intr_alert_reg(interrupts,
                                 'INTR_ENABLE',
                                 'Interrupt Enable Register',
                                 lambda w, n: ('Enable interrupt when '
                                               '{}!!INTR_STATE.{} is set.'
                                               .format('corresponding bit in '
                                                       if w else '',
                                                       n)),
                                 'rw',
                                 'hro',
                                 False,
                                 [])
        self._add_intr_alert_reg(interrupts,
                                 'INTR_TEST',
                                 'Interrupt Test Register',
                                 lambda w, n: ('Write 1 to force '
                                               '{}!!INTR_STATE.{} to 1.'
                                               .format('corresponding bit in '
                                                       if w else '',
                                                       n)),
                                 'wo',
                                 'hro',
                                 True,
                                 # intr_test csr is WO so reads back 0s
                                 ["excl:CsrNonInitTests:CsrExclWrite"])

    def make_alert_regs(self, alerts: List[Alert]) -> None:
        assert alerts
        assert len(alerts) < self._reg_width
        self._add_intr_alert_reg(alerts,
                                 'ALERT_TEST',
                                 'Alert Test Register',
                                 ('Write 1 to trigger '
                                  'one alert event of this kind.'),
                                 'wo',
                                 'hro',
                                 True,
                                 [])

    def get_addr_width(self) -> int:
        '''Calculate the number of bits to address every byte of the block'''
        return (self.offset - 1).bit_length()

    def has_shadowed_reg(self) -> bool:
        '''Returns true if reg block contains shadowed regs'''
        for r in self.flat_regs:
            if r.shadowed:
                return True

        return False

    def has_internal_shadowed_reg(self) -> bool:
        '''Returns true if reg block contains shadowed regs in internal regs'''
        for r in self.flat_regs:
            if r.shadowed and not r.hwext:
                return True

        return False
