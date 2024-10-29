# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import re
from collections.abc import MutableMapping
from typing import Dict, Iterator, List, Optional, Tuple

from reggen.lib import check_keys, check_str, check_int, check_bool, check_list

REQUIRED_FIELDS = {
    'name': ['s', "name of the item"],
}

OPTIONAL_FIELDS = {
    'desc': ['s', "description of the item"],
    'type': ['s', "item type. int by default"],
    'default': ['s', "item default value"],
    'local': ['pb', "to be localparam"],
    'expose': ['pb', "to be exposed to top"],
    'randcount': [
        's', "number of bits to randomize in the parameter. 0 by default."
    ],
    'randtype': ['s', "type of randomization to perform. none by default"],
    'unpacked_dimensions': [
        's', "unpacked dimensions of parameter e.g. [16] for a single unpacked "
             "dimension of size 16. none by default"],
}


class BaseParam:
    def __init__(self,
                 name: str,
                 desc: Optional[str],
                 param_type: str,
                 unpacked_dimensions: Optional[str]):
        self.name = name
        self.desc = desc
        self.param_type = param_type
        self.unpacked_dimensions = unpacked_dimensions

    def apply_default(self, value: str) -> None:
        if self.param_type[:3] == 'int':
            check_int(value,
                      'default value for parameter {} '
                      '(which has type {})'
                      .format(self.name, self.param_type))
        self.default = value

    def as_dict(self) -> Dict[str, object]:
        rd = {}  # type: Dict[str, object]
        rd['name'] = self.name
        if self.desc is not None:
            rd['desc'] = self.desc
        rd['type'] = self.param_type
        if self.unpacked_dimensions is not None:
            rd['unpacked_dimensions'] = self.unpacked_dimensions
        return rd


class LocalParam(BaseParam):
    def __init__(self,
                 name: str,
                 desc: Optional[str],
                 param_type: str,
                 unpacked_dimensions: Optional[str],
                 value: str):
        super().__init__(name, desc, param_type, unpacked_dimensions)
        self.value = value

    def expand_value(self, when: str) -> int:
        try:
            return int(self.value, 0)
        except ValueError:
            raise ValueError("When {}, the {} value expanded as "
                             "{}, which doesn't parse as an integer."
                             .format(when, self.name, self.value)) from None

    def as_dict(self) -> Dict[str, object]:
        rd = super().as_dict()
        rd['local'] = True
        rd['default'] = self.value
        return rd


class Parameter(BaseParam):
    def __init__(self,
                 name: str,
                 desc: Optional[str],
                 param_type: str,
                 unpacked_dimensions: Optional[str],
                 default: str,
                 expose: bool):
        super().__init__(name, desc, param_type, unpacked_dimensions)
        self.default = default
        self.expose = expose

    def as_dict(self) -> Dict[str, object]:
        rd = super().as_dict()
        rd['default'] = self.default
        rd['expose'] = 'true' if self.expose else 'false'
        return rd


class RandParameter(BaseParam):
    def __init__(self,
                 name: str,
                 desc: Optional[str],
                 param_type: str,
                 randcount: int,
                 randtype: str):
        assert randcount > 0
        assert randtype in ['perm', 'data']
        super().__init__(name, desc, param_type, None)
        self.randcount = randcount
        self.randtype = randtype

    def apply_default(self, value: str) -> None:
        raise ValueError('Cannot apply a default value of {!r} to '
                         'parameter {}: it is a random netlist constant.'
                         .format(self.name, value))

    def as_dict(self) -> Dict[str, object]:
        rd = super().as_dict()
        rd['randcount'] = self.randcount
        rd['randtype'] = self.randtype
        return rd


class MemSizeParameter(BaseParam):
    def __init__(self,
                 name: str,
                 desc: Optional[str],
                 param_type: str):
        super().__init__(name, desc, param_type, None)


def _parse_parameter(where: str, raw: object) -> BaseParam:
    rd = check_keys(raw, where,
                    list(REQUIRED_FIELDS.keys()),
                    list(OPTIONAL_FIELDS.keys()))

    # TODO: Check if PascalCase or ALL_CAPS
    name = check_str(rd['name'], 'name field of ' + where)

    r_desc = rd.get('desc')
    if r_desc is None:
        desc = None
    else:
        desc = check_str(r_desc, 'desc field of ' + where)

    r_unpacked_dimensions = rd.get('unpacked_dimensions')
    if r_unpacked_dimensions is None:
        unpacked_dimensions = None
    else:
        unpacked_dimensions = \
            check_str(r_unpacked_dimensions,
                      'unpacked_dimensions field of ' + where)

    # TODO: We should probably check that any register called RndCnstFoo has
    #       randtype and randcount.
    if name.lower().startswith('rndcnst') and 'randtype' in rd:
        # This is a random netlist constant and should be parsed as a
        # RandParameter.
        randtype = check_str(rd.get('randtype', 'none'),
                             'randtype field of ' + where)
        if randtype not in ['perm', 'data']:
            raise ValueError('At {}, parameter {} has a name that implies it '
                             'is a random netlist constant, which means it '
                             'must specify a randtype of "perm" or "data", '
                             'rather than {!r}.'
                             .format(where, name, randtype))

        r_randcount = rd.get('randcount')
        if r_randcount is None:
            raise ValueError('At {}, the random netlist constant {} has no '
                             'randcount field.'
                             .format(where, name))
        randcount = check_int(r_randcount, 'randcount field of ' + where)
        if randcount <= 0:
            raise ValueError('At {}, the random netlist constant {} has a '
                             'randcount of {}, which is not positive.'
                             .format(where, name, randcount))

        r_type = rd.get('type')
        if r_type is None:
            raise ValueError('At {}, parameter {} has no type field (which is '
                             'required for random netlist constants).'
                             .format(where, name))
        param_type = check_str(r_type, 'type field of ' + where)

        local = check_bool(rd.get('local', 'false'), 'local field of ' + where)
        if local:
            raise ValueError('At {}, the parameter {} specifies local = true, '
                             'meaning that it is a localparam. This is '
                             'incompatible with being a random netlist '
                             'constant (how would it be set?)'
                             .format(where, name))

        r_default = rd.get('default')
        if r_default is not None:
            raise ValueError('At {}, the parameter {} specifies a value for '
                             'the "default" field. This is incompatible with '
                             'being a random netlist constant: the value will '
                             'be set by the random generator.'
                             .format(where, name))

        expose = check_bool(rd.get('expose', 'false'),
                            'expose field of ' + where)
        if expose:
            raise ValueError('At {}, the parameter {} specifies expose = '
                             'true, meaning that the parameter is exposed to '
                             'the top-level. This is incompatible with being '
                             'a random netlist constant.'
                             .format(where, name))

        return RandParameter(name, desc, param_type, randcount, randtype)

    # This doesn't have a name like a random netlist constant. Check that it
    # doesn't define randcount or randtype.
    for fld in ['randcount', 'randtype']:
        if fld in rd:
            raise ValueError("At {where}, the parameter {name} specifies "
                             "{fld} but the name doesn't look like a random "
                             "netlist constant. To use {fld}, prefix the name "
                             "with RndCnst."
                             .format(where=where, name=name, fld=fld))

    if name.lower().startswith('memsize'):
        r_type = rd.get('type')
        if r_type is None:
            raise ValueError('At {}, parameter {} has no type field (which is '
                             'required for memory size parameters).'
                             .format(where, name))
        param_type = check_str(r_type, 'type field of ' + where)

        if rd.get('type') != "int":
            raise ValueError('At {}, memory size parameter {} must be of type integer.'
                             .format(where, name))

        local = check_bool(rd.get('local', 'false'), 'local field of ' + where)
        if local:
            raise ValueError('At {}, the parameter {} specifies local = true, '
                             'meaning that it is a localparam. This is '
                             'incompatible with being a memory size parameter.'
                             .format(where, name))

        expose = check_bool(rd.get('expose', 'false'),
                            'expose field of ' + where)
        if expose:
            raise ValueError('At {}, the parameter {} specifies expose = '
                             'true, meaning that the parameter is exposed to '
                             'the top-level. This is incompatible with '
                             'being a memory size parameter.'
                             .format(where, name))

        return MemSizeParameter(name, desc, param_type)

    r_type = rd.get('type')
    if r_type is None:
        param_type = 'int'
    else:
        param_type = check_str(r_type, 'type field of ' + where)

    local = check_bool(rd.get('local', 'true'), 'local field of ' + where)
    expose = check_bool(rd.get('expose', 'false'), 'expose field of ' + where)

    r_default = rd.get('default')
    if r_default is None:
        raise ValueError('At {}, the {} param has no default field.'
                         .format(where, name))
    else:
        default = check_str(r_default, 'default field of ' + where)
        if param_type[:3] == 'int':
            check_int(default,
                      'default field of {}, (an integer parameter)'
                      .format(name))

    if local:
        if expose:
            raise ValueError('At {}, the localparam {} cannot be exposed to '
                             'the top-level.'
                             .format(where, name))
        return LocalParam(name, desc, param_type, unpacked_dimensions,
                          value=default)
    else:
        return Parameter(name, desc, param_type, unpacked_dimensions,
                         default, expose)


# Note: With a modern enough Python, we'd like this to derive from
#       "MutableMapping[str, BaseParam]". Unfortunately, the MutableMapping
#       class only become subscriptable in Python 3.9. So we derive from just
#       "MutableMapping" and tell mypy not to worry about it.
class Params(MutableMapping):  # type: ignore
    def __init__(self) -> None:
        self.by_name = {}  # type: Dict[str, BaseParam]

    def __getitem__(self, key: str) -> BaseParam:
        return self.by_name[key]

    def __delitem__(self, key: str) -> None:
        del self.by_name[key]

    def __setitem__(self, key: str, value: BaseParam) -> None:
        self.by_name[key] = value

    def __iter__(self) -> Iterator[str]:
        return iter(self.by_name)

    def __len__(self) -> int:
        return len(self.by_name)

    def __repr__(self) -> str:
        return f"{type(self).__name__}({self.by_name})"

    def add(self, param: BaseParam) -> None:
        assert param.name not in self.by_name
        self.by_name[param.name] = param

    def apply_defaults(self, defaults: List[Tuple[str, str]]) -> None:
        for idx, (key, value) in enumerate(defaults):
            param = self.by_name[key]
            if param is None:
                raise KeyError('Cannot find parameter '
                               '{} to set default value.'
                               .format(key))

            param.apply_default(value)

    def _expand_one(self, value: str, when: str) -> int:
        # Check whether value is already an integer: if so, return that.
        try:
            return int(value, 0)
        except ValueError:
            pass

        param = self.by_name.get(value)
        if param is None:
            raise ValueError('Cannot find a parameter called {} when {}. '
                             'Known parameters: {}.'
                             .format(value,
                                     when,
                                     ', '.join(self.by_name.keys())))

        # Only allow localparams in the expansion (because otherwise we're at
        # the mercy of whatever instantiates the block).
        if not isinstance(param, LocalParam):
            raise ValueError("When {}, {} is a not a local parameter."
                             .format(when, value))

        return param.expand_value(when)

    def expand(self, value: str, where: str) -> int:
        # Here, we want to support arithmetic expressions with + and -. We
        # don't support other operators, or parentheses (so can parse with just
        # a regex).
        #
        # Use re.split, capturing the operators. This turns e.g. "a + b-c" into
        # ['a ', '+', ' b', '-', 'c']. If there's a leading operator ("+a"),
        # the first element of the results is an empty string. This means
        # elements with odd positions are always operators and elements with
        # even positions are values.
        acc = 0
        is_neg = False

        for idx, tok in enumerate(re.split(r'([+-])', value)):
            if idx == 0 and not tok:
                continue
            if idx % 2:
                is_neg = (tok == '-')
                continue

            term = self._expand_one(tok.strip(),
                                    'expanding term {} of {}'
                                    .format(idx // 2, where))
            acc += -term if is_neg else term

        return acc

    def as_dicts(self) -> List[Dict[str, object]]:
        return [p.as_dict() for p in self.by_name.values()]


class ReggenParams(Params):
    @staticmethod
    def from_raw(where: str, raw: object) -> 'ReggenParams':
        ret = ReggenParams()
        rl = check_list(raw, where)
        for idx, r_param in enumerate(rl):
            entry_where = 'entry {} in {}'.format(idx + 1, where)
            param = _parse_parameter(entry_where, r_param)
            if param.name in ret:
                raise ValueError('At {}, found a duplicate parameter with '
                                 'name {}.'
                                 .format(entry_where, param.name))
            ret.add(param)
        return ret

    def get_localparams(self) -> List[LocalParam]:
        ret = []
        for param in self.by_name.values():
            if isinstance(param, LocalParam):
                ret.append(param)
        return ret
