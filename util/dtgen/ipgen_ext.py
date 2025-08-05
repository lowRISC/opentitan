# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""This extension generates extra DT fields automatically based on the `dtgen`
instructions in the ipconfig.
"""

from .helper import IpHelper, Extension, StructType, ScalarType
from topgen.lib import Name
from typing import Optional
from jsonschema import validate
from dataclasses import dataclass

# Map from scalar type names (used in `dtgen`) to tuples:
# - C type name
# - Default value to return if the dt function is called with
#   an invalid argument
SCALAR_TYPES = {
    "uint8": {
        "c_typename": "uint8_t",
        "c_invalid_value": 0,
    },
    "uint16": {
        "c_typename": "uint16_t",
        "c_invalid_value": 0,
    },
}

# Schema of the "dtgen" attribute in the ipconfig.
dtgen_schema = {
    "type": "object",
    "patternProperties": {
        ".*": {
            "type": "object",
            "properties": {
                "type": {
                    "type": "string",
                    "enum": list(SCALAR_TYPES.keys()),
                },
                "name": {
                    "type": "string",
                    "pattern": "^[a-zA-Z_]+[a-zA-Z0-9_]*$",
                },
                "doc": {
                    "type": "string",
                }
            },
            "required": ["type"],
        }
    }
}

SCALAR_GETTER_HDR_TEMPLATE = """
/**
 * Get the {docshort}.
 *
 * @param dt Instance of {ipname}.
 * @return {docshort}.
 */
{rettype} dt_{ipname}_{fnname}(dt_{ipname}_t dt);
"""

SCALAR_GETTER_SRC_TEMPLATE = """
{rettype} dt_{ipname}_{fnname}(dt_{ipname}_t dt) {{
  return TRY_GET_DT(dt, {invalid_value})->ipgen_ext.{attrname};
}}
"""


@dataclass
class IpgenDtGenParam:
    type: str
    value: object
    name: str
    doc: str

    @staticmethod
    def from_raw(param_name: str, value: object, dtgen: dict[str, object]) -> "IpgenDtGenParam":
        name = dtgen.get('name', param_name)
        return IpgenDtGenParam(type = dtgen['type'], value = value, name = name,
                               doc = dtgen.get('doc', ""))


@dataclass
class IpgenDtGen:
    params: list[IpgenDtGenParam]

    @staticmethod
    def from_ipconfig(ipconfig: dict[str, object]) -> "IpgenDtGen":
        param_values = ipconfig["param_values"]
        dtgen = ipconfig.get('dtgen', {})
        validate(instance = dtgen, schema = dtgen_schema)
        params = []
        for (name, param) in dtgen.items():
            if name not in param_values:
                raise ValueError(f"dtgen refers to ipconfig parameter '{name}' " +
                                 "which does not appear in 'param_values'")
            params.append(IpgenDtGenParam.from_raw(name, param_values[name], param))
        return IpgenDtGen(params = params)


class IpgenExt(Extension):
    def __init__(self, ip_helper: IpHelper):
        self.ip_helper = ip_helper
        # Ignore IPs without ipconfig
        assert self.ip_helper.ipconfig, "IpgenExt requires ipconfig"
        assert "dtgen" in self.ip_helper.ipconfig, "IpgenExt requires ipconfig.dtgen"

        self.dtgen = IpgenDtGen.from_ipconfig(self.ip_helper.ipconfig)

    def create_ext(ip_helper: IpHelper) -> Optional["Extension"]:
        if ip_helper.ipconfig and 'dtgen' in ip_helper.ipconfig:
            return IpgenExt(ip_helper)

    def extend_dt_ip(self) -> tuple[Name, StructType]:
        st = StructType()

        for param in self.dtgen.params:
            # At the moment, only simple scalar types are supported
            st.add_field(
                name = Name.from_snake_case(param.name),
                field_type = ScalarType(SCALAR_TYPES[param.type]["c_typename"]),
                docstring = param.doc,
            )

        return Name(["ipgen_ext"]), st

    def fill_dt_ip(self, m) -> dict:
        values = {}

        for param in self.dtgen.params:
            values[Name.from_snake_case(param.name)] = param.value

        return values

    def render_dt_ip(self, pos: Extension.DtIpPos) -> str:
        res = ""
        if pos == Extension.DtIpPos.HeaderEnd:
            # Generate one function per attribute
            for param in self.dtgen.params:
                res += SCALAR_GETTER_HDR_TEMPLATE.format(
                    rettype = SCALAR_TYPES[param.type]["c_typename"],
                    ipname = self.ip_helper.ip_name.as_snake_case(),
                    fnname = param.name,
                    docshort = param.doc,
                )
        elif pos == Extension.DtIpPos.SourceEnd:
            # Generate one function per attribute
            for param in self.dtgen.params:
                res += SCALAR_GETTER_SRC_TEMPLATE.format(
                    rettype = SCALAR_TYPES[param.type]["c_typename"],
                    ipname = self.ip_helper.ip_name.as_snake_case(),
                    fnname = param.name,
                    attrname = param.name,
                    docshort = param.doc,
                    invalid_value = SCALAR_TYPES[param.type]["c_invalid_value"],
                )

        return res
