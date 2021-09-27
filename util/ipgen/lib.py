# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from typing import Dict, Optional, Union, cast

import hjson  # type: ignore
from reggen.lib import check_int, check_keys, check_list, check_name, check_str
from reggen.params import BaseParam, Params


class TemplateParseError(Exception):
    pass


class TemplateParameter(BaseParam):
    """ A template parameter. """
    def __init__(self, name: str, desc: Optional[str], param_type: str,
                 default: str):
        super().__init__(name, desc, param_type)
        self.default = default
        self.value = None

    def as_dict(self) -> Dict[str, object]:
        rd = super().as_dict()
        rd['default'] = self.default
        return rd


def _parse_template_parameter(where: str, raw: object) -> TemplateParameter:
    rd = check_keys(raw, where, ['name', 'desc', 'type'], ['default'])

    name = check_str(rd['name'], 'name field of ' + where)

    r_desc = rd.get('desc')
    if r_desc is None:
        desc = None
    else:
        desc = check_str(r_desc, 'desc field of ' + where)

    r_type = rd.get('type')
    param_type = check_str(r_type, 'type field of ' + where)
    if not param_type in ('string', 'int'):
        raise ValueError('At {}, the {} param has an invalid type field {!r}. '
                         'Allowed values are: string, int.'.format(
                             where, name, param_type))

    r_default = rd.get('default')
    default = check_str(r_default, 'default field of ' + where)
    if param_type[:3] == 'int':
        check_int(default,
                  'default field of {}, (an integer parameter)'.format(name))

    return TemplateParameter(name, desc, param_type, default)


class TemplateParams(Params):
    """ A group of template parameters. """
    @classmethod
    def from_raw(cls, where: str, raw: object) -> 'TemplateParams':
        """ Produce a TemplateParams instance from an object as it is in Hjson.
        """
        ret = cls()
        rl = check_list(raw, where)
        for idx, r_param in enumerate(rl):
            entry_where = 'entry {} in {}'.format(idx + 1, where)
            param = _parse_template_parameter(entry_where, r_param)
            if param.name in ret:
                raise ValueError('At {}, found a duplicate parameter with '
                                 'name {}.'.format(entry_where, param.name))
            ret.add(param)
        return ret


class IpTemplate:
    """ An IP template.

    An IP template is an IP block which needs to be parametrized before it
    can be transformed into an actual IP block (which can then be instantiated
    in a hardware design).
    """

    name: str
    params: Params
    template_path: Path

    def __init__(self, name: str, params: Params, template_path: Path):
        self.name = name
        self.params = params
        self.template_path = template_path

    @classmethod
    def from_template_path(cls, template_path: Path) -> 'IpTemplate':
        """ Create an IpTemplate from a template directory.

        An IP template directory has a well-defined structure:

        - The IP template name (TEMPLATE_NAME) is equal to the directory name.
        - It contains a file 'data/TEMPLATE_NAME.tpldesc.hjson' containing all
          configuration information related to the template.
        - It contains zero or more files ending in '.tpl'. These files are
          Mako templates and rendered into an file in the same location without
          the '.tpl' file extension.
        """

        # Check if the directory structure matches expectations.
        if not template_path.is_dir():
            raise TemplateParseError(
                "Template path {!r} is not a directory.".format(
                    str(template_path)))
        if not (template_path / 'data').is_dir():
            raise TemplateParseError(
                "Template path {!r} does not contain the required 'data' directory."
                .format(str(template_path)))

        # The template name equals the name of the template directory.
        template_name = template_path.stem

        # Find the template description file.
        tpldesc_file = template_path / 'data/{}.tpldesc.hjson'.format(
            template_name)

        # Read the template description from file.
        try:
            tpldesc_obj = hjson.load(open(tpldesc_file, 'r'), use_decimal=True)
        except (OSError, FileNotFoundError) as e:
            raise TemplateParseError(
                "Unable to read template description file {!r}: {}".format(
                    str(tpldesc_file), str(e)))

        # Parse the template description file.
        where = 'template description file {!r}'.format(str(tpldesc_file))
        if 'template_param_list' not in tpldesc_obj:
            raise TemplateParseError(
                f"Required key 'variables' not found in {where}")

        try:
            params = TemplateParams.from_raw(
                f"list of parameters in {where}",
                tpldesc_obj['template_param_list'])
        except ValueError as e:
            raise TemplateParseError(e) from None

        return cls(template_name, params, template_path)


def check_param_dict(obj: object, what: str) -> Dict[str, Union[int, str]]:
    """ Check that obj is a dict with str keys and int or str values. """
    if not isinstance(obj, dict):
        raise ValueError(
            "{} is expected to be a dict, but was actually a {}.".format(
                what,
                type(obj).__name__))

    for key, value in obj.items():
        if not isinstance(key, str):
            raise ValueError(
                '{} has a key {!r}, which is not a string.'.format(what, key))

        if not (isinstance(value, str) or isinstance(value, int)):
            raise ValueError(f"key {key} of {what} has a value {value!r}, "
                             "which is neither a str, nor an int.")

    return cast(Dict[str, Union[int, str]], obj)


class IpConfig:
    def __init__(self,
                 instance_name: str,
                 param_values: Dict[str, Union[str, int]] = {}):
        self.instance_name = instance_name
        self.param_values = param_values

    @classmethod
    def from_raw(cls, raw: object, where: str) -> 'IpConfig':
        """ Load an IpConfig from a raw object """

        rd = check_keys(raw, 'configuration file ' + where, ['instance_name'],
                        ['param_values'])
        instance_name = check_name(rd.get('instance_name'),
                                   "the key 'instance_name' of " + where)

        param_values = check_param_dict(rd.get('param_values', []),
                                        f"the key 'param_values' of {where}")

        return cls(instance_name, param_values)

    @classmethod
    def from_text(cls, txt: str, where: str) -> 'IpConfig':
        """Load an IpConfig from an Hjson description in txt"""
        return cls.from_raw(
            hjson.loads(txt, use_decimal=True, encoding="UTF-8"), where)

    def to_file(self, file_path: Path, header: Optional[str] = ""):
        obj = {}
        obj['instance_name'] = self.instance_name
        obj['param_values'] = str(self.param_values)

        with open(file_path, 'w') as fp:
            if header:
                fp.write(header)
            hjson.dump(obj,
                       fp,
                       ensure_ascii=False,
                       use_decimal=True,
                       for_json=True,
                       encoding='UTF-8',
                       indent=2)
            fp.write("\n")
