# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Mapping, Optional, Sequence

from reggen.bits import Bits
from reggen.lib import (PART_PRIMARY, check_keys, check_name, check_str, check_int, check_list,
                        check_bool, check_partition, check_partition_order)
from reggen.params import Parameter, ReggenParams


class Signal:

    def __init__(self, name: str, desc: str, bits: Bits, partition: str,
                 enabled_after_reset: bool = False,
                 width_param: Optional[Parameter] = None):
        self.name = name
        self.desc = desc
        self.bits = bits
        self.partition = partition
        self.enabled_after_reset = enabled_after_reset
        # The exposed parameter that sets the width of the signal, if any.  In that case, bits has
        # the width given by the default value of the parameter.
        self.width_param = width_param

    @staticmethod
    def from_raw(what: str, lsb: int, raw: object) -> 'Signal':
        return Signal._from_raw(what, lsb, raw, None)

    @staticmethod
    def _from_raw(what: str, lsb: int, raw: object,
                  params: Optional[ReggenParams]) -> 'Signal':
        '''Parse a signal

        If params is given, the width field may name an exposed parameter of the block.  This
        allows each instance of the block to set the width of the signal.
        '''
        rd = check_keys(raw, what, ["name", "desc"],
                        ["width", "enabled_after_reset", "partition"])

        name = check_name(rd['name'], 'name field of ' + what)
        desc = check_str(rd['desc'], 'desc field of ' + what)
        r_width = rd.get('width', 1)
        width_param = None
        if params is not None and isinstance(r_width, str):
            param = params.get(r_width)
            if param is not None:
                if not isinstance(param, Parameter) or not param.expose:
                    raise ValueError(f'The width field of signal {name} ({what}) refers to '
                                     f'parameter {r_width}, which is not exposed to the top '
                                     'level.')
                width_param = param
        if width_param is not None:
            width = check_int(width_param.default,
                              f'default value of parameter {r_width}, the width field of ' + what)
        else:
            width = check_int(r_width, 'width field of ' + what)
        enabled_after_reset = check_bool(rd.get("enabled_after_reset", False),
                                         "enabled_after_reset field of " + what)
        partition = check_partition(rd.get("partition", PART_PRIMARY),
                                    "partition field of " + what)

        if width <= 0:
            raise ValueError(f'The width field of signal {name} ({what}) '
                             f'has value {width}, but should be positive.')

        bits = Bits(lsb + width - 1, lsb)

        return Signal(name, desc, bits, partition, enabled_after_reset, width_param)

    @staticmethod
    def from_raw_list(what: str, raw: object) -> Sequence['Signal']:
        return Signal._from_raw_list(what, raw, None)

    @staticmethod
    def io_list_from_raw(what: str, raw: object,
                         params: ReggenParams) -> Sequence['Signal']:
        '''Parse a list of chip IO signals

        The width field of each signal may name an exposed parameter of the block.
        '''
        return Signal._from_raw_list(what, raw, params)

    @staticmethod
    def _from_raw_list(what: str, raw: object,
                       params: Optional[ReggenParams]) -> Sequence['Signal']:
        # A signal's bit index is its position in the list, so each partition's
        # signals must be declared as a contiguous, primary-first run.
        raw_list = check_list(raw, what)
        check_partition_order(raw_list, what)

        lsb = 0
        ret = []
        for idx, entry in enumerate(raw_list):
            entry_what = 'entry {} of {}'.format(idx, what)
            interrupt = Signal._from_raw(entry_what, lsb, entry, params)
            ret.append(interrupt)
            lsb += interrupt.bits.width()
        return ret

    def width(self, param_values: Optional[Mapping[str, object]] = None) -> int:
        '''Return the width of the signal

        If the width is set by a parameter, param_values (e.g. the param_decl field of a top-level
        instance) can override the default value of that parameter.
        '''
        if self.width_param is None or param_values is None:
            return self.bits.width()
        name = self.width_param.name
        if name not in param_values:
            return self.bits.width()
        width = check_int(param_values[name],
                          f'value of parameter {name}, the width of {self.name}')
        if width <= 0:
            raise ValueError(f'The width of signal {self.name} is set by parameter {name} to '
                             f'{width}, but should be positive.')
        return width

    def name_width(self) -> str:
        '''Return the name of the signal followed by its width, if it is not a single bit'''
        if self.width_param is not None:
            return f'{self.name}[{self.width_param.name}-1:0]'
        if self.bits.width() == 1:
            return self.name
        return f'{self.name}[{self.bits.msb}:0]'

    def _asdict(self) -> Dict[str, object]:
        ret: Dict[str, object] = {
            'name': self.name,
            'desc': self.desc,
            'width': (self.width_param.name if self.width_param is not None
                      else str(self.bits.width()))
        }
        # Only emit the partition information for items belonging to the secondary partition.
        # Note, this item cannot differentiate if it belongs to a split IP or not. Therefore,
        # we don't emit the partition information for items of the primary partition to avoid
        # polluting the output for a non-split IP.
        if self.partition != PART_PRIMARY:
            ret['partition'] = self.partition
        return ret

    def as_nwt_dict(self, type_field: str,
                    param_values: Optional[Mapping[str, object]] = None) -> Dict[str, object]:
        '''Return a view of the signal as a dictionary

        The dictionary has fields "name", "width" and "type", the last
        of which comes from the type_field argument. Used for topgen
        integration. param_values is passed to width().

        '''
        ret = {
            'name': self.name,
            'width': self.width(param_values),
            'type': type_field
        }
        # Only emit the partition information for items belonging to the secondary partition.
        # Note, this item cannot differentiate if it belongs to a split IP or not. Therefore,
        # we don't emit the partition information for items of the primary partition to avoid
        # polluting the output for a non-split IP.
        if self.partition != PART_PRIMARY:
            ret['partition'] = self.partition
        return ret
