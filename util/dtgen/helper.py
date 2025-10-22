# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from abc import ABC, abstractmethod
from typing import Optional
from collections import OrderedDict
from collections.abc import Mapping
from enum import Enum

from basegen.lib import Name
from topgen.lib import CEnum, CArrayMapping, find_modules
from reggen.ip_block import IpBlock

import logging


def indent_text(text, indent):
    return "".join(indent + line for line in text.splitlines(True))


class BaseType(ABC):
    @abstractmethod
    def render_type_def(self) -> str:
        """
        Render the type definition.

        Example: "struct X {int field;};"
        """

    @abstractmethod
    def render_var_decl(self, name: Name) -> str:
        """
        Render the declaration of a variable with this type and the name
        in argument.

        Example (name="my_var"): "int my_var"
        """

    @abstractmethod
    def render_value(self, value: object) -> str:
        """
        Render a value of this type.
        """

    def render_var_def(self, name: Name, value: object) -> str:
        """
        Render the definition of a variable with this type.

        Example (name="my_var"): "int my_var = 42"
        """
        return "{} = {};".format(self.render_var_decl(name), self.render_value(value))


class ScalarType(BaseType):
    def __init__(self, base_type: object):
        """
        Wrapper around the following types:
        - str: values are also str and rendered as-is
        - Name/CEnum: values are Name() and the Name/enum name
            is prefixed to the value which is rendered using .as_c_enum()
        """
        self.base_type = base_type

        assert isinstance(self.base_type, Name) or isinstance(self.base_type, str), \
            "except either a Name or str as base type, not {}".format(type(self.base_type))

    def render_type_def(self) -> str:
        return ""

    def _render_type(self) -> str:
        if isinstance(self.base_type, Name):
            return self.base_type.as_c_type()

        if isinstance(self.base_type, str):
            return self.base_type

        assert False, "I don't know how to render a {}".format(type(self.base_type))

    def render_var_decl(self, name: Name) -> str:
        return "{} {}".format(self._render_type(), name.as_snake_case())

    def render_value(self, value: object) -> str:
        if isinstance(self.base_type, Name):
            assert isinstance(value, Name), \
                "ScalarType({}) can only render a Name(), not {}".format(self.base_type, value)
            return (self.base_type + value).as_c_enum()

        if isinstance(self.base_type, str):
            return value

        assert False, "I don't know how to render a {}".format(type(self.base_type))


class ArrayMapType(BaseType):
    """
    An array type that maps values to other values.
    """
    def __init__(self, elem_type: BaseType, index_type: BaseType, length: object):
        self.elem_type = elem_type
        self.index_type = index_type
        self.length = length

    def render_type_def(self) -> str:
        return ""

    def render_var_decl(self, name: Name) -> str:
        return "{}[{}]".format(self.elem_type.render_var_decl(name),
                               self.index_type.render_value(self.length))

    def render_value(self, value: object):
        assert isinstance(value, Mapping), "ArrayMapType can only render value which are mappings"
        text = ""
        for (entry, value) in value.items():
            text += "[{}] = {},\n".format(self.index_type.render_value(entry),
                                          self.elem_type.render_value(value))
        return "{\n" + indent_text(text, "  ") + "}"


class StructType(BaseType):
    """
    This class holds the description of a struct. It allows nesting
    of structures as well as arbitrary types. If the name is left to
    None, this is considered an anonymous structure which can be
    nested in another struct.
    """

    def __init__(self, name: Optional[Name] = None):
        self.name = name
        self.fields = OrderedDict()
        self.internal = False

    def __str__(self) -> str:
        return "StructType{{name={}, {}}}".format(self.name, self.fields.keys())

    def add_field(self, name: Name, field_type: BaseType, docstring: str = ""):
        assert name not in self.fields, \
            f"cannot add field {name} to struct since it already exists"
        self.fields[name] = (field_type, docstring)

    def has_field(self, name: Name) -> bool:
        return name in self.fields

    def field_type(self, name: Name) -> object:
        return self.fields[name][0]

    def as_c_type(self) -> str:
        assert self.name is not None, "cannot get the name of an anonymous StructType"
        return self.name.as_c_type()

    def _render_type_def(self) -> str:
        text = ""
        for (name, (field_type, docstring)) in self.fields.items():
            if len(docstring.splitlines()) > 1:
                predocstring = "/**\n{}\n */\n".format(indent_text(docstring, " * "))
                postdocstring = ""
            elif len(docstring.splitlines()) == 1:
                predocstring, postdocstring = "", " /**< {} */".format(docstring)
            else:
                predocstring, postdocstring = "", ""
            text += predocstring + field_type.render_var_decl(name) + ";" + postdocstring + "\n"

        if self.name is None:
            st_name = ""
        else:
            st_name = self.name.as_snake_case() + " "
        text = "struct " + st_name + \
            "{\n" + indent_text(text, "  ") + "}"
        return text

    def render_type_def(self) -> str:
        text = ""
        # Only render non-anonymous typedef
        if self.name is not None:
            text += "typedef " + self._render_type_def() + " " + self.name.as_c_type() + ";\n"
        return text

    def render_var_decl(self, name: Name) -> str:
        # Anonymous structures need to include the type definition.
        if self.name is None:
            typename = self._render_type_def()
        else:
            typename = self.name.as_c_type()
        return "{} {}".format(typename, name.as_snake_case())

    def render_value(self, value: Mapping) -> str:
        """
        Render a value which is a dictionary mapping fields to value.
        """
        assert isinstance(value, Mapping), "StructType can only render values which are mappings"
        text = ""
        unused_keys = set(value.keys())
        for (name, (field_type, _)) in self.fields.items():
            assert isinstance(name, Name), "StructType can only render mappings with `Name` keys"
            if name not in value:
                logging.warning("field {} not found in {}".format(name, value))
                continue
            text += ".{} = {},\n".format(name.as_snake_case(), field_type.render_value(value[name]))
            unused_keys.remove(name)
        assert not unused_keys, \
            "Extra keys when rendering {} of type {}: {}".format(value, self, list(unused_keys))

        return "{\n" + indent_text(text, "  ") + "}"


class DefinesBlock:
    """
    A block of C `#define`s.
    """
    def __init__(self):
        self.defines = {}

    def add_define(self, name: Name, value: object):
        self.defines[name] = value

    def render(self) -> str:
        text = ""
        for (name, value) in self.defines.items():
            if value is None:
                text += "#define {}\n".format(name.as_c_define())
            else:
                text += "#define {} {}\n".format(name.as_c_define(), str(value))
        return text


class Extension(ABC):
    """
    Base class for extensions.
    """
    @staticmethod
    @abstractmethod
    def create_ext(ip_helper: "IpHelper") -> Optional["Extension"]:
        """
        This function must return an extension if it wants to modify
        the DT of the IP passed to the constructor. Otherwise it must
        return `None`.
        """

    def extend_dt_ip(self) -> Optional[tuple[Name, StructType]]:
        """
        Override this function to add some fields to the structure storing
        fields for a given IP. This method MUST not modify `ip_helper` but
        it can access its public fields. Return `None` if you don't want to
        add more fields. Otherwise return a tuple (name, struct): the ext
        struct will be placed in the DT struct under the name `name`.
        """

    def fill_dt_ip(self, m) -> Optional[dict]:
        """
        Override this function to return the content of the fields added in
        `extend_dt_ip` for a given module instance `m`. All fields MUST
        be filled. This method MUST not modify `ip_helper` but
        it can access its public fields.
        """

    class DtIpPos(Enum):
        """Represent a position in `dt_ip.{c,h}` where a template can be inserted"""
        HeaderEnd = 0  # At the end of `dt_<ip>.h`
        SourceEnd = 1  # At the end of `dt_<ip>.c`
        SourceIncludes = 2  # At the include stage of `dt_<ip>.c`
        HeaderIncludes = 3  # At the include stage of `dt_<ip>.h`

    def render_dt_ip(self, pos: DtIpPos) -> str:
        """
        Return a string that will be inserted in the dt_<ip>.{c,h} file at a given position.
        """
        return ""


class TopGenHelper:
    """
    We cannot easily import the TopGen class from topgen.lib so we need to replicate some
    of the logic when it comes to type/enum naming. This helper classes encapsulats this logic.
    """
    def __init__(self, topcfg):
        self.top = topcfg

    def irq_id_type_name(self, plic_name: str) -> Name:
        """
        Given a PLIC name, return the full naem of the `irq_id_t` type.
        """
        return Name(["top"]) + Name.from_snake_case(self.top["name"]) + \
            Name.from_snake_case(plic_name.removeprefix("rv_")) + Name(["irq", "id"])


class TopHelper:
    """
    Helper class to generate dt_api.{c,h}.
    """
    DT_INSTANCE_ID_NAME = Name(["dt", "instance", "id"])
    DT_DEVICE_TYPE_NAME = Name(["dt", "device", "type"])
    DT_CLOCK_ENUM_NAME = Name(["dt", "clock"])
    DT_RESET_ENUM_NAME = Name(["dt", "reset"])
    DT_PAD_NAME = Name(["dt", "pad"])
    DT_PAD_DESC_NAME = Name(["dt", "pad", "desc"])

    DT_PERIPH_IO_NAME = Name(["dt", "periph", "io"])
    DT_PERIPH_IO_TYPE_FIELD_NAME = Name(["type"])
    DT_PERIPH_IO_TYPE_ENUM_NAME = Name.from_snake_case("dt_periph_io_type")
    DT_PERIPH_IO_DIR_FIELD_NAME = Name(["dir"])
    DT_PERIPH_IO_DIR_ENUM_NAME = Name.from_snake_case("dt_periph_io_dir")
    DT_PERIPH_IO_PERIPH_IN_DIO_PAD_FIELD_NAME = Name.from_snake_case("periph_input_or_direct_pad")
    DT_PERIPH_IO_OUTSEL_FIELD_NAME = Name.from_snake_case("outsel_or_dt_pad")

    DT_PAD_NAME = Name(["dt", "pad"])
    DT_PAD_STRUCT_NAME = Name(["dt", "pad", "desc"])
    DT_PAD_TYPE_FIELD_NAME = Name(["type"])
    DT_PAD_TYPE_ENUM_NAME = Name.from_snake_case("dt_pad_type")
    DT_PAD_MIO_OUT_DIO_FIELD_NAME = Name.from_snake_case("mio_out_or_direct_pad")
    DT_PAD_INSEL_FIELD_NAME = Name(["insel"])

    KNOWN_PORT_TYPES = ["input", "output", "inout", "`INOUT_AO"]

    def __init__(self, topcfg, enum_type, array_mapping_type):
        self.top = topcfg
        self._top_name = Name(["top"]) + Name.from_snake_case(topcfg["name"])
        self._topgen = TopGenHelper(topcfg)

        assert enum_type in [CEnum], "Unsupported enum type"
        assert array_mapping_type in [CArrayMapping], \
               "Unsupported array mapping type"
        self._enum_type = enum_type
        self._array_mapping_type = array_mapping_type

        self.addr_space = "hart"

        self._module_types = sorted({m["type"] for m in topcfg["module"]})

        self._init_api()
        self._init_pads()
        self._init_irq_map()
        if self.has_alert_handler():
            self._init_alert_map()
        self._init_dev_type_map()

    def _init_api(self):
        """
        Create all API types/enums.
        """
        # List of all module instance types (i.e. uart, aes, etc)
        # and put them in an enum.
        self.device_type_enum = self._enum_type(Name([]), self.DT_DEVICE_TYPE_NAME)
        self.device_type_enum.add_constant(Name(["unknown"]), "Instance of unknown type")
        for module_name in self._module_types:
            self.device_type_enum.add_constant(
                Name.from_snake_case(module_name),
                f"instance of {module_name}"
            )
        if isinstance(self.device_type_enum, CEnum):
            self.device_type_enum.add_count_constant("Number of instance types")

        # List of all module instance IDs and put them in an enum.
        self.instance_id_enum = self._enum_type(Name([]), self.DT_INSTANCE_ID_NAME)
        self.instance_id_enum.add_constant(Name(["unknown"]), "Unknown instance")
        for module_name in self._module_types:
            modules = [m for m in self.top["module"] if m["type"] == module_name]
            for m in modules:
                self.instance_id_enum.add_constant(
                    Name.from_snake_case(m["name"]),
                    "instance {} of {}".format(m["name"], m["type"])
                )
        if isinstance(self.instance_id_enum, CEnum):
            self.instance_id_enum.add_count_constant("Number of instance IDs")

        # List all muxed pads directly from the top.
        pads = [pad for pad in self.top['pinout']['pads'] if pad['connection'] == 'muxed']
        # List direct pads from the pinmux to avoid pins which are not relevant.
        if self.top.get("pinmux", {}).get("ios"):
            pads += [pad for pad in self.top['pinmux']['ios'] if pad['connection'] != 'muxed']

        # List all pads and put them in an enum.
        self.pad_enum = self._enum_type(Name([]), self.DT_PAD_NAME)
        self._pad_map = OrderedDict()
        for pad in pads:
            name = pad['name']
            if 'width' in pad and pad['width'] > 1:
                name += str(pad['idx'])
            self._pad_map[name] = pad
            # Direct pads usually do not have a description, instead the "pad" attribute
            # points to the actual pad in top.pinout.pads which contains the details.
            if pad["connection"] == "direct":
                desc = None
                for io_pad in self.top["pinout"]["pads"]:
                    if io_pad["name"] == pad["pad"]:
                        desc = io_pad["desc"]
                        break
                if desc is None:
                    logging.warning(f"could not find description of pad {name}:" +
                                    " could not find {} in pinout.pads".format(pad["pad"]))
                    desc = ""
            else:
                desc = pad["desc"]
            self.pad_enum.add_constant(
                Name.from_snake_case(name),
                desc
            )
        if isinstance(self.pad_enum, CEnum):
            self.pad_enum.add_count_constant("Number of pads")

        # List of all clocks and put them in an enum.
        self.clock_enum = self._enum_type(Name([]), self.DT_CLOCK_ENUM_NAME)
        clocks = self.top['clocks']
        for clock in clocks["srcs"] + clocks["derived_srcs"]:
            clock_name = Name.from_snake_case(clock["name"])
            self.clock_enum.add_constant(clock_name, "clock {}".format(clock["name"]))

        # Unmanaged clocks
        for clock in self.top['unmanaged_clocks']:
            clock_name = Name.from_snake_case(clock)
            self.clock_enum.add_constant(clock_name)

        self.clock_enum.add_count_constant("Number of clocks")

        # List of all reset nodes and put them in an enum.
        self.reset_enum = self._enum_type(Name([]), self.DT_RESET_ENUM_NAME)
        self.reset_enum.add_constant(Name(["unknown"]), "Unknown reset")
        for reset_node in self.top["resets"]["nodes"]:
            reset_name = Name.from_snake_case(reset_node["name"])
            self.reset_enum.add_constant(reset_name, "Reset node {}".format(reset_node["name"]))

        # Unmanaged resets
        for reset in self.top['unmanaged_resets']:
            reset_name = Name.from_snake_case(reset)
            self.reset_enum.add_constant(reset_name)

        self.reset_enum.add_count_constant("Number of resets")

        # Create structure to describe a peripheral I/O and a pad.
        self._create_periph_io_struct()
        self._create_pad_struct()

    def _create_periph_io_struct(self):
        """
        Create a structure to represent a peripheral I/O.
        """
        self.periph_io_struct = StructType(self.DT_PERIPH_IO_NAME)
        # In C, we want to make the fields private to we wrap them in a nested
        # "__internal" struct.
        st = StructType()
        self.periph_io_struct.add_field(
            name = Name(["__internal"]),
            field_type = st,
            docstring = "Private fields",
        )

        st.add_field(
            name = self.DT_PERIPH_IO_TYPE_FIELD_NAME,
            field_type = ScalarType(self.DT_PERIPH_IO_TYPE_ENUM_NAME),
            docstring = "Peripheral I/O type",
        )
        st.add_field(
            name = self.DT_PERIPH_IO_DIR_FIELD_NAME,
            field_type = ScalarType(self.DT_PERIPH_IO_DIR_ENUM_NAME),
            docstring = "Peripheral I/O direction",
        )
        st.add_field(
            name = self.DT_PERIPH_IO_PERIPH_IN_DIO_PAD_FIELD_NAME,
            field_type = ScalarType("uint16_t"),
            docstring = """For `kDtPeriphIoTypeMio`: peripheral input number. This is the index of the MIO_PERIPH_INSEL register
that controls this peripheral I/O.

For `kDtPeriphIoTypeDio`: DIO pad number. This is the index of the various DIO_PAD_* registers
that control this peripheral I/O.""",  # noqa:E501
        )
        st.add_field(
            name = self.DT_PERIPH_IO_OUTSEL_FIELD_NAME,
            field_type = ScalarType("uint16_t"),
            docstring = """For `kDtPeriphIoTypeMio`: peripheral output number. This is the value to put in the MIO_OUTSEL registers
to connect an output to this peripheral I/O. For `kDtPeriphIoTypeDio`: the pad index (`dt_pad_t`) to which this I/O is connected.""",  # noqa:E501
        )

    def _create_pad_struct(self):
        """
        Create a structure to represent a pad.
        """
        self.pad_struct = StructType(self.DT_PAD_STRUCT_NAME)
        self.pad_struct.add_field(
            name = self.DT_PAD_TYPE_FIELD_NAME,
            field_type = ScalarType(self.DT_PAD_TYPE_ENUM_NAME),
            docstring = "Pad type",
        )
        self.pad_struct.add_field(
            name = self.DT_PAD_MIO_OUT_DIO_FIELD_NAME,
            field_type = ScalarType("uint16_t"),
            docstring = """For `kDtPadTypeMio` pads: MIO out number. This is the index of the MIO_OUTSEL register
that controls this pad (or the output part of this pad).

For `kDtPadTypeDio`:  DIO pad number. This is the index of the various DIO_PAD_* registers
that control this pad.""",  # noqa:E501
        )
        self.pad_struct.add_field(
            name = self.DT_PAD_INSEL_FIELD_NAME,
            field_type = ScalarType("uint16_t"),
            docstring = """For `kDtPadTypeMio` pads: MIO pad number. This is the value to put in the MIO_PERIPH_INSEL
registers to connect a peripheral to this pad.""",  # noqa:E501
        )

    def _init_pads(self):
        """
        Create an array mapping for the list of all pads.
        """
        self.pad_dt_map = ArrayMapType(
            elem_type = self.pad_struct,
            index_type = ScalarType(self.pad_enum.name),
            length = Name(["count"])
        )
        self.pad_dt_values = OrderedDict()
        for (padname, pad) in self._pad_map.items():
            topname = self.top["name"]
            if pad["connection"] == "muxed":
                pad_type = Name.from_snake_case("mio")
                pad_mio_out_or_direct_pad = "0"
                pad_insel = "0"
                assert pad["port_type"] in self.KNOWN_PORT_TYPES, \
                    "unexpected pad port type '{}'".format(pad["port_type"])
                if pad["port_type"] in ["input", "inout", "`INOUT_AO"]:
                    pad_mio_out_or_direct_pad = \
                        Name.from_snake_case(f"top_{topname}_pinmux_mio_out_{padname}").as_c_enum()
                if pad["port_type"] in ["output", "inout", "`INOUT_AO"]:
                    pad_insel = \
                        Name.from_snake_case(f"top_{topname}_pinmux_insel_{padname}").as_c_enum()
            # Follow the same logic as in toplevel_pkg.sv.tpl and topgen/lib.py: the pads
            # non-muxed enumerated from pinmux.ios are all direct pads for the pinmux.
            else:
                pad_type = Name.from_snake_case("dio")
                pad_mio_out_or_direct_pad = \
                    Name.from_snake_case(f"top_{topname}_direct_pads_{padname}").as_c_enum()
                pad_insel = "0"
            self.pad_dt_values[Name.from_snake_case(padname)] = {
                self.DT_PAD_TYPE_FIELD_NAME: pad_type,
                self.DT_PAD_MIO_OUT_DIO_FIELD_NAME: pad_mio_out_or_direct_pad,
                self.DT_PAD_INSEL_FIELD_NAME: pad_insel,
            }

    def _init_irq_map(self):
        """
        Create the array mappings to dispatch interrupts.
        """

        plic_names = [m["name"] for m in find_modules(self.top["module"], "rv_plic")]
        assert len(plic_names) == 1, "dtgen assumes that there is exactly one PLIC"
        self.the_plic_irq_id_type_name = self._topgen.irq_id_type_name(plic_names[0])

        self.inst_from_irq_map = ArrayMapType(
            elem_type = ScalarType(self.instance_id_enum.name),
            index_type = ScalarType(self.the_plic_irq_id_type_name),
            length = Name(["count"])
        )
        self.inst_from_irq_values = OrderedDict(
            {Name(["none"]): Name(["unknown"])},
        )
        for intr in self.top["interrupt"]:
            width = int(intr["width"])
            for i in range(width):
                name = Name.from_snake_case(intr["name"])
                if width > 1:
                    name += Name([str(i)])
                if intr["incoming"]:
                    module_name = Name(["unknown"])
                else:
                    module_name = Name.from_snake_case(intr["module_name"])
                self.inst_from_irq_values[name] = module_name

    def has_alert_handler(self):
        # FIXME find a better way then just hardcoding this module name
        return any(module["name"] == "alert_handler" for module in self.top["module"])

    def _init_alert_map(self):
        """
        Create the array mappings to dispatch alerts.
        """
        self.inst_from_alert_map = ArrayMapType(
            elem_type = ScalarType(self.instance_id_enum.name),
            index_type = ScalarType(Name(["top"]) +
                                    Name.from_snake_case(self.top["name"]) +
                                    Name(["alert", "id"])),
            length = Name(["count"])
        )
        self.inst_from_alert_values = OrderedDict()
        for alert in self.top["alert"]:
            width = int(alert["width"])
            for i in range(width):
                name = Name.from_snake_case(alert["name"])
                if width > 1:
                    name += Name([str(i)])
                self.inst_from_alert_values[name] = Name.from_snake_case(
                    alert["module_name"])

    def _init_dev_type_map(self):
        """
        Create an array mapping from instance ID to device type.
        """
        self.dev_type_map = ArrayMapType(
            elem_type = ScalarType(self.device_type_enum.name),
            index_type = ScalarType(self.instance_id_enum.name),
            length = Name(["count"]),
        )
        self.dev_type_values = OrderedDict()
        for module_name in self._module_types:
            for m in self.top["module"]:
                if m["type"] != module_name:
                    continue
                self.dev_type_values[Name.from_snake_case(m["name"])] = \
                    Name.from_snake_case(module_name)

    def get_module_type(self, module_name: str) -> str:
        """
        Return the module type from a module name.
        """
        for m in self.top["module"]:
            if m["name"] == module_name:
                return m["type"]
        raise RuntimeError("module '{}' not found in top '{}'".format(module_name, self._top_name))


class IpHelper:
    UNNAMED_REG_BLOCK_NAME = "core"
    INST_ID_FIELD_NAME = Name(["inst", "id"])
    REG_BLOCK_ADDR_FIELD_NAME = Name(["reg", "addr"])
    MEM_ADDR_FIELD_NAME = Name(["mem", "addr"])
    MEM_SIZE_FIELD_NAME = Name(["mem", "size"])
    CLOCK_FIELD_NAME = Name(["clock"])
    RESET_FIELD_NAME = Name(["reset"])
    PERIPH_IO_FIELD_NAME = Name(["periph", "io"])
    DT_STRUCT_NAME_PREFIX = Name(["dt", "desc"])
    FIRST_IRQ_FIELD_NAME = Name(["first", "irq"])
    FIRST_ALERT_FIELD_NAME = Name(["first", "alert"])
    EXTENSION_FIELD_NAME = Name(["ext"])

    def __init__(self, top_helper: TopHelper, ip: IpBlock, ipconfig: object, default_node: str,
                 enum_type: object, array_mapping_type: object,
                 extension_cls: Optional[list[Extension]] = None):
        self.top_helper = top_helper
        self.top = top_helper.top
        self.ip = ip
        self.ipconfig = ipconfig
        self.default_node = default_node
        self.ip_name = Name.from_snake_case(self.ip.name)

        assert enum_type in [CEnum], "Unsupported enum type"
        assert array_mapping_type in [CArrayMapping], \
               "Unsupported array mapping type"
        self._enum_type = enum_type
        self._array_mapping_type = array_mapping_type

        # TODO: discover automatically or take that as argument.
        self._addr_space = "hart"
        # Name to assign to the unnamed reg block (if any)
        if self.default_node is None:
            self.default_node = self.UNNAMED_REG_BLOCK_NAME

        self._init_reg_blocks()
        self._init_memories()
        self._init_irqs()
        self._init_alerts()
        self._init_clocks()
        self._init_wakeups()
        self._init_reset_requests()
        self._init_resets()
        self._init_periph_io()
        self._init_features()
        self.extensions = list(filter(lambda x: x is not None,
                                      [ext_cls.create_ext(self)
                                       for ext_cls in extension_cls or []]))

        self._init_instances()

    def _init_reg_blocks(self):
        reg_blocks = []
        for rb in self.ip.reg_blocks.keys():
            if rb is None:
                reg_blocks.append(self.UNNAMED_REG_BLOCK_NAME)
            else:
                reg_blocks.append(rb)

        # If there are no register blocks, we don't need to validate default_node
        if reg_blocks:
            assert self.default_node in reg_blocks, \
                "default node ({}) is invalid".format(self.default_node)

        self.reg_block_enum = self._enum_type(
            Name([]), Name(["dt"]) + self.ip_name + Name(["reg", "block"]))
        for rb in reg_blocks:
            self.reg_block_enum.add_constant(Name.from_snake_case(rb))
        if isinstance(self.reg_block_enum, CEnum):
            self.reg_block_enum.add_count_constant("Number of register blocks")

    def _init_memories(self):
        memories = list(self.ip.memories.keys())

        self.memory_enum = self._enum_type(
            Name([]), Name(["dt"]) + self.ip_name + Name(["memory"]))
        for mem in memories:
            self.memory_enum.add_constant(Name.from_snake_case(mem))
        if isinstance(self.memory_enum, CEnum):
            self.memory_enum.add_count_constant("Number of memories")

    def has_irqs(self):
        return len(self.ip.interrupts) > 0

    def _init_irqs(self):
        device_irqs = OrderedDict()
        for sig in self.ip.interrupts:
            if sig.bits.width() > 1:
                for bit in range(sig.bits.width()):
                    device_irqs[sig.name + str(bit)] = sig
            else:
                device_irqs[sig.name] = sig

        self.irq_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name + Name(["irq"]))
        for (irq, sig) in device_irqs.items():
            self.irq_enum.add_constant(Name.from_snake_case(irq), sig.desc)
        if isinstance(self.reg_block_enum, CEnum):
            self.irq_enum.add_count_constant("Number of IRQs")

    def has_alerts(self):
        return len(self.ip.alerts) > 0

    def has_alert_handler(self):
        # FIXME find a better way then just hardcoding this module name
        return any(module["name"] == "alert_handler" for module in self.top["module"])

    def _init_alerts(self):
        device_alerts = OrderedDict()
        for sig in self.ip.alerts:
            if sig.bits.width() > 1:
                for bit in range(sig.bits.width()):
                    device_alerts[sig.name + str(bit)] = sig
            else:
                device_alerts[sig.name] = sig

        self.alert_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name + Name(["alert"]))
        for (alert, sig) in device_alerts.items():
            self.alert_enum.add_constant(Name.from_snake_case(alert), sig.desc)
        if isinstance(self.reg_block_enum, CEnum):
            self.alert_enum.add_count_constant("Number of Alerts")

    def has_clocks(self):
        return len(self._device_clocks) > 0

    def _init_clocks(self):
        # We only care about external clocks.
        self._device_clocks = self.ip.clocking.clock_signals(False)
        # Remove the scan clock
        if "scan_clk_i" in self._device_clocks:
            self._device_clocks.remove("scan_clk_i")

        self.clock_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name + Name(["clock"]))
        self.clock_map = OrderedDict()
        for clk in self._device_clocks:
            clk_orig = clk
            # Remove the clk_ prefix and _i suffix of clocks.
            assert clk.startswith("clk_") and clk.endswith("_i"), \
                f"clock '{clk}' does not start with clk_ and end with _i"
            # There is a special case: if the clock name is "clk_i" then we don't want an empty name
            if clk == "clk_i":
                clk = "clk"
            else:
                clk = clk.removeprefix("clk_").removesuffix("_i")
            self.clock_map[clk_orig] = clk
            self.clock_enum.add_constant(Name.from_snake_case(clk), f"Clock port {clk_orig}")
        if isinstance(self.reg_block_enum, CEnum):
            self.clock_enum.add_count_constant("Number of clock ports")

    def has_reset_requests(self):
        return len(self.reset_req_map) > 0

    def simplify_reset_request_name(self, req: str) -> str:
        # Remove the rst_req prefix or suffix
        if req.startswith("rst_req_"):
            req = req.removeprefix("rst_req_")
        if req.endswith("_rst_req"):
            req = req.removesuffix("_rst_req")
        return req

    def _init_reset_requests(self):
        self.reset_req_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name +
                                              Name(["reset", "req"]))
        self.reset_req_map = OrderedDict()
        # Resets are listed alongside clocks.
        for req in self.ip.reset_requests:
            desc = req.desc
            req = req.name
            req_orig = req
            req = self.simplify_reset_request_name(req)

            self.reset_req_map[req_orig] = req
            self.reset_req_enum.add_constant(Name.from_snake_case(req), desc)
        if isinstance(self.reset_req_enum, CEnum):
            self.reset_req_enum.add_count_constant("Number of reset requests")

    def has_resets(self):
        return len(self.reset_map) > 0

    def _init_resets(self):
        self.reset_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name + Name(["reset"]))
        self.reset_map = OrderedDict()
        # Resets are listed alongside clocks.
        for rst in self.ip.clocking.reset_signals():
            rst_orig = rst
            # Remove the rst_ prefix and _ni suffix.
            assert rst.startswith("rst_") and rst.endswith("_ni"), \
                f"reset '{rst}' does not start with rst_ and end with _ni"
            # There is a special case: if the reset name is "rst_ni" then we would get a weird name.
            if rst == "rst_ni":
                rst = "rst"
            else:
                rst = rst.removeprefix("rst_").removesuffix("_ni")
            self.reset_map[rst_orig] = rst
            self.reset_enum.add_constant(Name.from_snake_case(rst), f"Reset port {rst_orig}")
        if isinstance(self.reset_enum, CEnum):
            self.reset_enum.add_count_constant("Number of reset ports")

    def has_periph_io(self):
        return len(self._device_signals) > 0

    def _init_periph_io(self):
        inouts, inputs, outputs = self.ip.xputs
        self._device_signals = OrderedDict()
        for sig in inputs + outputs + inouts:
            if sig.bits.width() > 1:
                for bit in range(sig.bits.width()):
                    self._device_signals[sig.name + str(bit)] = (sig.name, bit)
            else:
                self._device_signals[sig.name] = (sig.name, -1)

        self.periph_io_enum = self._enum_type(
            Name([]),
            Name(["dt"]) + self.ip_name + Name(["periph", "io"])
        )
        for sig in self._device_signals.keys():
            self.periph_io_enum.add_constant(Name.from_snake_case(sig))
        if isinstance(self.reg_block_enum, CEnum):
            self.periph_io_enum.add_count_constant("Number of peripheral I/O")

    def has_wakeups(self):
        return len(self.ip.wakeups) > 0

    def _init_wakeups(self):
        self.wakeup_enum = self._enum_type(
            Name([]),
            Name(["dt"]) + self.ip_name + Name(["wakeup"])
        )
        for sig in self.ip.wakeups:
            self.wakeup_enum.add_constant(Name.from_snake_case(sig.name), sig.desc)
        if isinstance(self.wakeup_enum, CEnum):
            self.wakeup_enum.add_count_constant("Number of wakeups")

    def _init_instances(self):
        self.inst_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name)
        self.inst_map = OrderedDict()
        self._create_dt_struct()
        self.inst_dt_map = ArrayMapType(
            elem_type = self.inst_struct,
            index_type = ScalarType(self.inst_enum.name),
            length = Name(["count"])
        )
        self.inst_dt_values = OrderedDict()
        self.first_inst_id = None
        self.last_inst_id = None
        for m in self.top["module"]:
            if m["type"] != self.ip.name:
                continue
            # Heuristic to make the name nicer, e.g. if the name is adc_ctrl_aon,
            # remove "adc_ctrl_" because every enum is already prefixed by adc_ctrl
            if m["name"].startswith(self.ip.name + "_"):
                inst_name = m["name"].removeprefix(self.ip.name + "_")
            elif m["name"].startswith(self.ip.name):
                inst_name = m["name"].removeprefix(self.ip.name)
            else:
                inst_name = m["name"]
            inst_name = Name.from_snake_case(inst_name) if inst_name != "" else Name([])
            self.inst_enum.add_constant(inst_name, m["name"])
            if self.first_inst_id is None:
                self.first_inst_id = TopHelper.DT_INSTANCE_ID_NAME + Name.from_snake_case(m["name"])
            self.last_inst_id = TopHelper.DT_INSTANCE_ID_NAME + Name.from_snake_case(m["name"])
            self.inst_dt_values[inst_name] = self._create_instance(m)
            self.inst_map[inst_name] = m
        if isinstance(self.inst_enum, CEnum):
            if self.inst_enum.constants:
                self.inst_enum.add_first_constant("First instance")
            self.inst_enum.add_count_constant("Number of instances")

    def has_reg_blocks(self):
        return len(self.ip.reg_blocks) > 0

    def has_features(self):
        return len(self.ip.features) > 0

    def _init_features(self):
        self.feature_defines = DefinesBlock()
        for feature in self.ip.features:
            define = Name(["opentitan"]) + self.ip_name + Name(["has"]) + Name([feature.name])
            self.feature_defines.add_define(define, 1)

    def _create_dt_struct(self):
        self.inst_struct = StructType(self.DT_STRUCT_NAME_PREFIX + self.ip_name)
        self.inst_struct.add_field(
            name = self.INST_ID_FIELD_NAME,
            field_type = ScalarType(TopHelper.DT_INSTANCE_ID_NAME),
            docstring = "Instance ID"
        )
        if self.has_reg_blocks():
            self.inst_struct.add_field(
                name = self.REG_BLOCK_ADDR_FIELD_NAME,
                field_type = ArrayMapType(
                    elem_type = ScalarType("uint32_t"),
                    index_type = ScalarType(self.reg_block_enum.name),
                    length = Name(["count"]),
                ),
                docstring = "Base address of each register block"
            )
        self.inst_struct.add_field(
            name = self.MEM_ADDR_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = ScalarType("uint32_t"),
                index_type = ScalarType(self.memory_enum.name),
                length = Name(["count"]),
            ),
            docstring = "Base address of each memory"
        )
        self.inst_struct.add_field(
            name = self.MEM_SIZE_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = ScalarType("uint32_t"),
                index_type = ScalarType(self.memory_enum.name),
                length = Name(["count"]),
            ),
            docstring = "Size in bytes of each memory"
        )
        if self.has_irqs():
            # FIXME We need to handle better the case where a block is not connected to the PLIC.
            self.inst_struct.add_field(
                name = self.FIRST_IRQ_FIELD_NAME,
                field_type = ScalarType(self.top_helper.the_plic_irq_id_type_name),
                docstring = """PLIC ID of the first IRQ of this instance

This can be `kDtPlicIrqIdNone` if the block is not connected to the PLIC."""
            )
        if self.has_alerts() and self.has_alert_handler():
            # FIXME We need to handle better the case where a block is
            # not connected to the Alert Handler.
            self.inst_struct.add_field(
                name = self.FIRST_ALERT_FIELD_NAME,
                field_type = ScalarType(Name(["top"]) +
                                        Name.from_snake_case(self.top["name"]) +
                                        Name(["alert", "id"])),
                docstring = """Alert ID of the first Alert of this instance.

This value is undefined if the block is not connected to the Alert Handler."""
            )
        if self.has_clocks():
            self.inst_struct.add_field(
                name = self.CLOCK_FIELD_NAME,
                field_type = ArrayMapType(
                    elem_type = ScalarType(TopHelper.DT_CLOCK_ENUM_NAME),
                    index_type = ScalarType(self.clock_enum.name),
                    length = Name(["count"]),
                ),
                docstring = "Clock signal connected to each clock port"
            )
        if self.has_resets():
            self.inst_struct.add_field(
                name = self.RESET_FIELD_NAME,
                field_type = ArrayMapType(
                    elem_type = ScalarType(TopHelper.DT_RESET_ENUM_NAME),
                    index_type = ScalarType(self.reset_enum.name),
                    length = Name(["count"]),
                ),
                docstring = "Reset signal connected to each reset port"
            )
        if self.has_periph_io():
            self.inst_struct.add_field(
                name = self.PERIPH_IO_FIELD_NAME,
                field_type = ArrayMapType(
                    elem_type = self.top_helper.periph_io_struct,
                    index_type = ScalarType(self.periph_io_enum.name),
                    length = Name(["count"]),
                ),
                docstring = "Description of each peripheral I/O"
            )
        # Add extension fields.
        self._extension_structs = {}
        for ext in self.extensions:
            ext_desc = ext.extend_dt_ip()
            if ext_desc:
                ext_name, ext_struct = ext_desc
                self.inst_struct.add_field(
                    name = ext_name,
                    field_type = ext_struct,
                    docstring = "Extension",
                )
                self._extension_structs[ext] = ext_name

    def _create_instance(self, m):
        """
        Fill the description structure of an instance.
        """
        modname = m["name"]
        inst_desc = OrderedDict()
        # Instance ID.
        inst_desc[self.INST_ID_FIELD_NAME] = Name.from_snake_case(modname)
        # Reg block address map.
        if self.has_reg_blocks():
            reg_block_map = OrderedDict()
            for rb in self.ip.reg_blocks.keys():
                rb_key = rb
                if rb is None:
                    rb = self.UNNAMED_REG_BLOCK_NAME
                    rb_key = "null"  # Due to json serializing, None appears as null.
                rb = Name.from_snake_case(rb)
                # It is possible that this module is not accessible in this
                # address space. In this case, return a dummy value.
                # FIXME Maybe find a better way of doing this.
                assert rb_key in m["base_addrs"]
                reg_block_map[rb] = m["base_addrs"][rb_key].get(self._addr_space, "0xffffffff")
            inst_desc[self.REG_BLOCK_ADDR_FIELD_NAME] = reg_block_map
        # Memories.
        mem_addr_map = OrderedDict()
        mem_size_map = OrderedDict()
        for mem in self.ip.memories.keys():
            mem_name = Name.from_snake_case(mem)
            # It is possible that this module is not accessible in this
            # address space. In this case, return a dummy value.
            # FIXME Maybe find a better way of doing this.
            assert mem in m["base_addrs"]
            mem_addr_map[mem_name] = m["base_addrs"][mem].get(self._addr_space, "0xffffffff")
            assert mem in m["memory"] and "size" in m["memory"][mem]
            mem_size_map[mem_name] = m["memory"][mem]["size"]
        inst_desc[self.MEM_ADDR_FIELD_NAME] = mem_addr_map
        inst_desc[self.MEM_SIZE_FIELD_NAME] = mem_size_map
        # Clock map.
        if self.has_clocks():
            inst_clock_map = OrderedDict()
            for (port, clock) in m["clock_srcs"].items():
                if port not in self.clock_map:
                    continue
                # The clock source can either be just a string with the clock name, e.g.
                #   clock_srcs: {clk_i: "main", clk_edn_i: "main"}
                # Or a dictionary with the clock name and group:
                #  clock_srcs: { clk_esc_i: { clock: io_div4, group: secure } }
                if isinstance(clock, str):
                    clk_name = clock
                else:
                    clk_name = clock["clock"]
                inst_clock_map[Name.from_snake_case(self.clock_map[port])] = \
                    Name.from_snake_case(clk_name)
            inst_desc[self.CLOCK_FIELD_NAME] = inst_clock_map
        # Reset map.
        if self.has_resets():
            inst_reset_map = OrderedDict()
            for (port, rst) in m["reset_connections"].items():
                inst_reset_map[Name.from_snake_case(self.reset_map[port])] = \
                    Name.from_snake_case(rst["name"])
            inst_desc[self.RESET_FIELD_NAME] = inst_reset_map
        # First IRQ
        if self.has_irqs():
            irqs_packed = [irq for irq in self.top["interrupt"] if irq["module_name"] == modname]
            irqs = []
            for irq in irqs_packed:
                irq_name = Name.from_snake_case(irq["name"])
                irq_width = int(irq["width"])
                if irq_width > 1:
                    for i in range(irq_width):
                        irqs.append(irq_name + Name([str(i)]))
                else:
                    irqs.append(irq_name)
            # It can happen that a block declares some interrupts but the block is not connected to
            # the PLIC. For example, on english breakfast, the rv_timer is directly connected to
            # Ibex and not to the PLIC. In this case, we set the first_irq to None.
            #
            # TODO Handle this better in the future.
            if len(irqs) == 0:
                first_irq = Name(["none"])
            else:
                first_irq = irqs[0]
            inst_desc[self.FIRST_IRQ_FIELD_NAME] = first_irq
        # First Alert
        if self.has_alerts() and self.has_alert_handler():
            alerts_packed = [alert for alert in self.top["alert"]
                             if alert["module_name"] == modname]
            alerts = []
            for alert in alerts_packed:
                alert_name = Name.from_snake_case(alert["name"])
                alert_width = int(alert["width"])
                if alert_width > 1:
                    for i in range(alert_width):
                        alerts.append(alert_name + Name([str(i)]))
                else:
                    alerts.append(alert_name)
            # Because the alert information is generated by topgen, if the block has alerts and
            # the top instantiates an Alert Handler, the alerts must be connected to the Alert
            # Handler. Assert to check this is the case.
            assert len(alerts) > 0, \
                   "An IP declares alerts but does not connect them to the Alert Handler."
            inst_desc[self.FIRST_ALERT_FIELD_NAME] = alerts[0]
        # Periph I/O
        if self.has_periph_io():
            periph_ios = OrderedDict()
            for (sig, (port, idx)) in self._device_signals.items():
                found = False
                for conn in self.top.get("pinmux", {}).get("ios", []):
                    if conn["name"] != m["name"] + "_" + port or idx != conn["idx"]:
                        continue
                    if found:
                        logging.warning(
                            f"multiple connections found for device {modname}, signal {sig}")
                    found = True
                    periph_ios[Name.from_snake_case(sig)] = \
                        self._create_periph_io_desc(modname, port, conn)
                # If no connections were found, create a manual one to fake it.
                if not found:
                    logging.warning(f"no connection found for device {modname}, signal {sig}")
                    periph_ios[Name.from_snake_case(sig)] = self._create_periph_io_missing_desc()
            inst_desc[self.PERIPH_IO_FIELD_NAME] = periph_ios
        # Add extension fields.
        for (ext, ext_field_name) in self._extension_structs.items():
            ext_fields = ext.fill_dt_ip(m)
            assert ext_fields is not None, \
                "extension did not return fields data despite creating extension fields"
            inst_desc[ext_field_name] = ext_fields

        return inst_desc

    def _create_periph_io_desc(self, modname, pin_name, conn):
        topname = self.top["name"]
        if conn["type"] == "input":
            pin_dir = "in"
        elif conn["type"] == "output":
            pin_dir = "out"
        else:
            assert conn["type"] == "inout", \
                "unexpected connection dir '{}'".format(conn["type"])
            pin_dir = "inout"

        if conn["idx"] != -1:
            pin_name += str(conn["idx"])
        if conn["connection"] == "muxed":
            pin_type = "Mio"
            pin_periph_input_or_direct_pad = "0"
            pin_outsel = "0"
            if conn["type"] in ["input", "inout"]:
                periph_in = f"top_{topname}_pinmux_peripheral_in_{modname}_{pin_name}"
                pin_periph_input_or_direct_pad = Name.from_snake_case(periph_in).as_c_enum()
            if conn["type"] in ["output", "inout"]:
                outsel = f"top_{topname}_pinmux_outsel_{modname}_{pin_name}"
                pin_outsel = Name.from_snake_case(outsel).as_c_enum()
        elif conn["connection"] == "direct":
            pin_type = "Dio"
            direct_pad = f"top_{topname}_direct_pads_{modname}_{pin_name}"
            pin_periph_input_or_direct_pad = Name.from_snake_case(direct_pad).as_c_enum()
            # Unfortunately, the top level has two distinct names for pads: the pads listed
            # in top.pinmux.pads and the ones in top.pinmux.ios. Since the pad list uses
            # names from top.pinmux.ios for DIOs, but that the connections use the names
            # from top.pinmux.pads, we need to map between the two.
            padname = None
            for io in self.top_helper._pad_map.values():
                if io["connection"] == "direct" and io["pad"] == conn["pad"]:
                    if padname is not None:
                        raise RuntimeError(
                            "found at least two IOs that maps to pad {}".format(conn["pad"]) +
                            ": {} and {}".format(padname, io["name"])
                        )
                    padname = Name.from_snake_case(io["name"])
                    # IOs have a width, we need to handle that
                    if int(io["width"]) > 1:
                        padname += Name([str(io["idx"])])
            if padname is None:
                raise RuntimeError("could not find IO that maps to pad {}".format(conn["pad"]))
            pad_index = self.top_helper.pad_enum.name + padname
            pin_outsel = pad_index.as_c_enum()
        else:
            assert conn["connection"] == "manual", \
                "unexpected connection type '{}'".format(conn["connection"])
            pin_periph_input_or_direct_pad = "0"
            pin_outsel = "0"
            pin_type = "Unspecified"

        return {
            Name(["__internal"]): {
                TopHelper.DT_PERIPH_IO_TYPE_FIELD_NAME: Name.from_snake_case(pin_type),
                TopHelper.DT_PERIPH_IO_DIR_FIELD_NAME: Name.from_snake_case(pin_dir),
                TopHelper.DT_PERIPH_IO_PERIPH_IN_DIO_PAD_FIELD_NAME: pin_periph_input_or_direct_pad,
                TopHelper.DT_PERIPH_IO_OUTSEL_FIELD_NAME: pin_outsel,
            }
        }

    def _create_periph_io_missing_desc(self):
        return {
            Name(["__internal"]): {
                TopHelper.DT_PERIPH_IO_TYPE_FIELD_NAME: Name(["unspecified"]),
                TopHelper.DT_PERIPH_IO_DIR_FIELD_NAME: Name(["inout"]),
                TopHelper.DT_PERIPH_IO_PERIPH_IN_DIO_PAD_FIELD_NAME: "0",
                TopHelper.DT_PERIPH_IO_OUTSEL_FIELD_NAME: "0",
            }
        }

    def render_extension(self, ip_pos: Extension.DtIpPos) -> str:
        out = ""
        for ext in self.extensions:
            out += "\n" + ext.render_dt_ip(ip_pos) + "\n"
        return out
