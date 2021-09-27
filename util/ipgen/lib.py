# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from typing import Any, Dict, Optional, Union

import hjson  # type: ignore
from reggen.lib import check_int, check_keys, check_list, check_name, check_str
from reggen.params import BaseParam, Params


class TemplateParseError(Exception):
    pass


class TemplateParameter(BaseParam):
    """ A template parameter. """
    VALID_PARAM_TYPES = (
        'int',
        'string',
    )

    def __init__(self, name: str, desc: Optional[str], param_type: str,
                 default: str):
        assert param_type in self.VALID_PARAM_TYPES

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
    if param_type not in TemplateParameter.VALID_PARAM_TYPES:
        raise ValueError('At {}, the {} param has an invalid type field {!r}. '
                         'Allowed values are: {}.'.format(
                             where, name, param_type,
                             ', '.join(TemplateParameter.VALID_PARAM_TYPES)))

    r_default = rd.get('default')
    if param_type == 'int':
        default = check_int(
            r_default,
            'default field of {}, (an integer parameter)'.format(name))
    elif param_type == 'string':
        default = check_str(r_default, 'default field of ' + where)
    else:
        assert False, f"Unknown parameter type found: {param_type!r}"

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
    params: TemplateParams
    template_path: Path

    def __init__(self, name: str, params: TemplateParams, template_path: Path):
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


class IpConfig:
    def __init__(self,
                 template_params: TemplateParams,
                 instance_name: str,
                 param_values: Dict[str, Union[str, int]] = {}):
        self.template_params = template_params
        self.instance_name = instance_name
        self.param_values = IpConfig._check_param_values(
            template_params, param_values)

    @staticmethod
    def _check_param_values(template_params: TemplateParams,
                            param_values: Any) -> Dict[str, Union[str, int]]:
        """Check if parameter values are valid.

        Returns the parameter values in typed form if successful, and throws
        a ValueError otherwise.
        """
        param_values_typed = {}
        for key, value in param_values.items():
            if not isinstance(key, str):
                raise ValueError(
                    f"The IP configuration has a key {key!r} which is not a "
                    "string.")

            if key not in template_params:
                raise ValueError(
                    f"The IP configuration has a key {key!r} which is a "
                    "valid parameter.")

            if template_params[key].param_type == 'string':
                param_value_typed = check_str(
                    value, f"the key {key} of the IP configuration")
            elif template_params[key].param_type == 'int':
                param_value_typed = check_int(
                    value, f"the key {key} of the IP configuration")
            else:
                assert True, "Unexpeced parameter type found, expand this check"

            param_values_typed[key] = param_value_typed

        return param_values_typed

    @classmethod
    def from_raw(cls, template_params: TemplateParams, raw: object,
                 where: str) -> 'IpConfig':
        """ Load an IpConfig from a raw object """

        rd = check_keys(raw, 'configuration file ' + where, ['instance_name'],
                        ['param_values'])
        instance_name = check_name(rd.get('instance_name'),
                                   "the key 'instance_name' of " + where)

        if not isinstance(raw, dict):
            raise ValueError(
                "The IP configuration is expected to be a dict, but was "
                "actually a " + type(raw).__name__)

        param_values = IpConfig._check_param_values(template_params,
                                                    rd['param_values'])

        return cls(template_params, instance_name, param_values)

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
