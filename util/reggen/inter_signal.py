# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Dict, Optional

from reggen.lib import (check_keys, check_name,
                        check_str, check_optional_str, check_int)
from reggen.params import Parameter


class InterSignal:
    def __init__(self,
                 name: str,
                 desc: Optional[str],
                 struct: str,
                 package: Optional[str],
                 signal_type: str,
                 act: str,
                 width,
                 default: Optional[str]):
        if isinstance(width, Parameter):
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
    def from_raw(params: dict, what: str, raw: object) -> 'InterSignal':
        rd = check_keys(raw, what,
                        ['name', 'struct', 'type', 'act'],
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

        try:
            width = check_int(rd.get('width', 1), 'width field of ' + what)
            if width <= 0:
                raise ValueError('width field of {} is not positive.'.format(what))
        except ValueError:
            # Value error raised since it is not an int, lets try toi find out if it is a parameter
            width = params.get(rd.get('width', ''))
            width.default = check_int(width.default, 'width field of ' + what)
            if width.default <= 0:
                raise ValueError('width field of {} is not positive.'.format(what))
            # Parameter must be exposed to create a top-level (local) param
            if not width.expose:
                raise ValueError('width field of {} is not exposed.'.format(what))


        default = check_optional_str(rd.get('default'),
                                     'default field of ' + what)

        return InterSignal(name, desc, struct, package,
                           signal_type, act, width, default)

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
