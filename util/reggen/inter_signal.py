# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Optional, Union

from reggen.lib import (check_int, check_keys, check_name, check_optional_str,
                        check_str)
from reggen.params import ReggenParams, Parameter


class InterSignal:

    def __init__(self, name: str, desc: Optional[str], struct: str,
                 package: Optional[str], signal_type: str, act: str,
                 width: Union[int, Parameter], default: Optional[str]):
        if isinstance(width, Parameter):
            if isinstance(width.default, int):
                assert 0 < width.default
        else:
            assert 0 < width
        self.name = name
        self.desc = desc
        self.struct = struct
        self.package = package
        self.signal_type = signal_type
        self.act = act
        self.width = width
        self.default = default

    @staticmethod
    def from_raw(params: ReggenParams, what: str,
                 raw: object) -> 'InterSignal':
        rd = check_keys(raw, what, ['name', 'struct', 'type', 'act'],
                        ['desc', 'package', 'width', 'default'])

        name = check_name(rd['name'], 'name field of ' + what)

        r_desc = rd.get('desc')
        if r_desc is None:
            desc = None
        else:
            desc = check_str(r_desc, 'desc field of ' + what)

        struct = check_str(rd['struct'], 'struct field of ' + what)

        r_package = rd.get('package')
        if r_package is None or r_package == '':
            package = None
        else:
            package = check_name(r_package, 'package field of ' + what)

        signal_type = check_name(rd['type'], 'type field of ' + what)
        act = check_name(rd['act'], 'act field of ' + what)

        default = check_optional_str(rd.get('default'),
                                     'default field of ' + what)
        width: Union[int, Parameter] = 1
        width_p = params.get(rd.get('width'), 1)
        if isinstance(width_p, Parameter):
            width_p.default = check_int(width_p.default,
                                        'width field of ' + what)
            if width_p.default <= 0:
                raise ValueError(f'width field of {what} is not positive.')
            # Parameter must be exposed to create a top-level (local) param
            if not width_p.expose:
                raise ValueError(f'width field of {what} is not exposed.')
            width = width_p
        else:
            width = check_int(rd.get('width', 1), 'width field of ' + what)
            if width <= 0:
                raise ValueError(f'width field of {what} is not positive.')

        return InterSignal(name, desc, struct, package, signal_type, act,
                           width, default)

    def _asdict(self) -> Dict[str, object]:
        ret = {'name': self.name}  # type: Dict[str, object]
        if self.desc is not None:
            ret['desc'] = self.desc
        ret['struct'] = self.struct
        if self.package is not None:
            ret['package'] = self.package
        ret['type'] = self.signal_type
        ret['act'] = self.act
        ret['width'] = self.width
        if self.default is not None:
            ret['default'] = self.default

        return ret

    def as_dict(self) -> Dict[str, object]:
        return self._asdict()
