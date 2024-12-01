# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Code representing a list of bus interfaces for a block'''

from typing import Dict, List, Optional, Tuple

from reggen.inter_signal import InterSignal
from reggen.lib import check_list, check_keys, check_str, check_optional_bool, check_optional_str


class BusInterfaces:
    def __init__(self,
                 has_unnamed_host: bool,
                 named_hosts: List[str],
                 host_async: Dict[Optional[str], str],
                 has_unnamed_device: bool,
                 named_devices: List[str],
                 device_async: Dict[Optional[str], str],
                 device_hier_paths: Dict[Optional[str], str],
                 racl_support: Dict[Optional[str], bool]):
        assert has_unnamed_device or named_devices
        assert len(named_hosts) == len(set(named_hosts))
        assert len(named_devices) == len(set(named_devices))

        self.has_unnamed_host = has_unnamed_host
        self.named_hosts = named_hosts
        self.host_async = host_async
        self.has_unnamed_device = has_unnamed_device
        self.named_devices = named_devices
        self.device_async = device_async
        self.device_hier_paths = device_hier_paths
        self.racl_support = racl_support

    @staticmethod
    def from_raw(raw: object, where: str) -> 'BusInterfaces':
        has_unnamed_host = False
        named_hosts = []
        host_async = {}

        has_unnamed_device = False
        named_devices = []
        device_async = {}
        device_hier_paths = {}
        racl_support_map = {}

        for idx, raw_entry in enumerate(check_list(raw, where)):
            entry_what = 'entry {} of {}'.format(idx + 1, where)
            ed = check_keys(raw_entry, entry_what,
                            ['protocol', 'direction'],
                            ['name', 'async', 'hier_path', 'racl_support'])

            protocol = check_str(ed['protocol'],
                                 'protocol field of ' + entry_what)
            if protocol != 'tlul':
                raise ValueError('Unknown protocol {!r} at {}'
                                 .format(protocol, entry_what))

            direction = check_str(ed['direction'],
                                  'direction field of ' + entry_what)
            if direction not in ['device', 'host']:
                raise ValueError('Unknown interface direction {!r} at {}'
                                 .format(direction, entry_what))

            name = check_optional_str(ed.get('name'),
                                      'name field of ' + entry_what)

            async_clk = check_optional_str(ed.get('async'),
                                           'async field of ' + entry_what)

            hier_path = check_optional_str(ed.get('hier_path'),
                                           'hier_path field of ' + entry_what)

            racl_support = check_optional_bool(ed.get('racl_support'),
                                               'racl_support field of ' + entry_what)

            if direction == 'host':
                if name is None:
                    if has_unnamed_host:
                        raise ValueError('Multiple un-named host '
                                         'interfaces at {}'
                                         .format(where))
                    has_unnamed_host = True
                else:
                    if name in named_hosts:
                        raise ValueError('Duplicate host interface '
                                         'with name {!r} at {}'
                                         .format(name, where))
                    named_hosts.append(name)

                if async_clk is not None:
                    host_async[name] = async_clk
                if hier_path is not None:
                    raise ValueError('Hier path is not supported for host'
                                     'interface with name {!r} at {}'
                                     .format(name, where))
            else:
                if name is None:
                    if has_unnamed_device:
                        raise ValueError('Multiple un-named device '
                                         'interfaces at {}'
                                         .format(where))
                    has_unnamed_device = True
                else:
                    if name in named_devices:
                        raise ValueError('Duplicate device interface '
                                         'with name {!r} at {}'
                                         .format(name, where))
                    named_devices.append(name)

                if async_clk is not None:
                    device_async[name] = async_clk

                if hier_path is not None:
                    device_hier_paths[name] = hier_path
                else:
                    device_hier_paths[name] = 'u_reg'

                racl_support_map[name] = bool(racl_support)

        if not (has_unnamed_device or named_devices):
            raise ValueError('No device interface at ' + where)

        return BusInterfaces(has_unnamed_host, named_hosts, host_async,
                             has_unnamed_device, named_devices,
                             device_async, device_hier_paths, racl_support_map)

    def has_host(self) -> bool:
        return bool(self.has_unnamed_host or self.named_hosts)

    def _interfaces(self) -> List[Tuple[bool, Optional[str]]]:
        ret = []  # type: List[Tuple[bool, Optional[str]]]
        if self.has_unnamed_host:
            ret.append((True, None))
        for name in self.named_hosts:
            ret.append((True, name))

        if self.has_unnamed_device:
            ret.append((False, None))
        for name in self.named_devices:
            ret.append((False, name))

        return ret

    @staticmethod
    def _if_dict(is_host: bool, name: Optional[str]) -> Dict[str, object]:
        ret = {
            'protocol': 'tlul',
            'direction': 'host' if is_host else 'device'
        }  # type: Dict[str, object]

        if name is not None:
            ret['name'] = name

        return ret

    def as_dicts(self) -> List[Dict[str, object]]:
        return [BusInterfaces._if_dict(is_host, name)
                for is_host, name in self._interfaces()]

    def get_port_name(self, is_host: bool, name: Optional[str]) -> str:
        if is_host:
            tl_suffix = 'tl_h'
        else:
            tl_suffix = 'tl_d' if self.has_host() else 'tl'

        return (tl_suffix if name is None
                else '{}_{}'.format(name, tl_suffix))

    def get_port_names(self, inc_hosts: bool, inc_devices: bool) -> List[str]:
        ret = []
        for is_host, name in self._interfaces():
            if not (inc_hosts if is_host else inc_devices):
                continue
            ret.append(self.get_port_name(is_host, name))
        return ret

    def _if_inter_signal(self,
                         is_host: bool,
                         name: Optional[str]) -> InterSignal:
        act = 'req' if is_host else 'rsp'
        return InterSignal(self.get_port_name(is_host, name),
                           None, 'tl', 'tlul_pkg', 'req_rsp', act, 1, None)

    def inter_signals(self) -> List[InterSignal]:
        return [self._if_inter_signal(is_host, name)
                for is_host, name in self._interfaces()]

    def has_interface(self, is_host: bool, name: Optional[str]) -> bool:
        if is_host:
            if name is None:
                return self.has_unnamed_host
            else:
                return name in self.named_hosts
        else:
            if name is None:
                return self.has_unnamed_device
            else:
                return name in self.named_devices

    def find_port_name(self, is_host: bool, name: Optional[str]) -> str:
        '''Look up the given host/name pair and return its port name.

        Raises a KeyError if there is no match.

        '''
        if not self.has_interface(is_host, name):
            called = ('with no name'
                      if name is None else 'called {!r}'.format(name))
            raise KeyError('There is no {} bus interface {}.'
                           .format('host' if is_host else 'device',
                                   called))

        return self.get_port_name(is_host, name)
