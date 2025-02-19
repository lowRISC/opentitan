# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from abc import ABC, abstractmethod
from typing import Optional
from collections import OrderedDict

from topgen.lib import CEnum, CArrayMapping, Name
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
    def render_value(self, value: object):
        """
        Render a value of this type.
        """

    def render_var_def(self, name: Name, value: object) -> str:
        """
        Render the definition of a variable with this type.

        Example (name="my_var"): "int my_var = 42"
        """
        return "{} = {};\n".format(self.render_var_decl(name), self.render_value(value))


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

    def render_value(self, value: dict[object, object]):
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
        self.fields[name] = (field_type, docstring)

    def has_field(self, name: Name) -> bool:
        return name in self.fields

    def field_type(self, name: Name) -> object:
        return self.fields[name][0]

    def as_c_type(self) -> str:
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

    def render_value(self, value: dict[Name, object]) -> str:
        """
        Render a value which is a dictionary mapping fields to value.
        """
        text = ""
        for (name, (field_type, _)) in self.fields.items():
            # TODO warn about missing fields?
            if name not in value:
                logging.warn("field {} not found in {}".format(name, value))
                continue
            text += ".{} = {},\n".format(name.as_snake_case(), field_type.render_value(value[name]))
            value.pop(name)
        assert not value, \
            "Extra keys when rendering {} of type {}: {}".format(value, self, value.keys())

        return "{\n" + indent_text(text, "  ") + "}"


class TopHelper:
    """
    Helper class to generate dt_api.{c,h}.
    """
    DT_INSTANCE_ID_NAME = Name(["dt", "instance", "id"])
    DT_DEVICE_TYPE_NAME = Name(["dt", "device", "type"])
    DT_CLOCK_ENUM_NAME = Name(["dt", "clock"])
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
            self.device_type_enum.add_constant(Name(["count"]), "Number of instance types")

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
            self.instance_id_enum.add_constant(Name(["count"]), "Number of instance IDs")

        # List all muxed pads directly from the top.
        pads = [pad for pad in self.top['pinout']['pads'] if pad['connection'] == 'muxed']
        # List direct pads from the pinmux to avoid pins which are not relevant.
        pads += [pad for pad in self.top['pinmux']['ios'] if pad['connection'] != 'muxed']

        # List all pads and put them in an enum.
        self.pad_enum = self._enum_type(Name([]), self.DT_PAD_NAME)
        self._pad_map = OrderedDict()
        for pad in pads:
            name = pad['name']
            if 'width' in pad and pad['width'] > 1:
                name += str(pad['idx'])
            self._pad_map[name] = pad
            self.pad_enum.add_constant(
                Name.from_snake_case(name),
            )
        if isinstance(self.pad_enum, CEnum):
            self.pad_enum.add_constant(Name(["count"]), "Number of pads")

        # List of all clocks and put them in an enum.
        self.clock_enum = self._enum_type(Name([]), self.DT_CLOCK_ENUM_NAME)
        clocks = self.top['clocks']
        for clock in clocks["srcs"] + clocks["derived_srcs"]:
            clock_name = Name.from_snake_case(clock["name"])
            self.clock_enum.add_constant(clock_name)
        self.clock_enum.add_constant(Name(["count"]), "Number of clocks")

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
            elif pad["connection"] == "direct":
                pad_type = Name.from_snake_case("dio")
                pad_mio_out_or_direct_pad = \
                    Name.from_snake_case(f"top_{topname}_direct_pads_{padname}").as_c_enum()
                pad_insel = "0"
            else:
                assert pad["connection"] == "manual", \
                    "unexpected connection type '{}'".format(pad["connection"])
                pad_mio_out_or_direct_pad = "0"
                pad_insel = "0"
                pad_type = Name.from_snake_case("unspecified")
            self.pad_dt_values[Name.from_snake_case(padname)] = {
                self.DT_PAD_TYPE_FIELD_NAME: pad_type,
                self.DT_PAD_MIO_OUT_DIO_FIELD_NAME: pad_mio_out_or_direct_pad,
                self.DT_PAD_INSEL_FIELD_NAME: pad_insel,
            }

    def _init_irq_map(self):
        """
        Create the array mappings to dispatch interrupts.
        """
        self.inst_from_irq_map = ArrayMapType(
            elem_type = ScalarType(self.instance_id_enum.name),
            index_type = ScalarType(Name(["top"]) +
                                    Name.from_snake_case(self.top["name"]) +
                                    Name(["plic", "irq", "id"])),
            length = Name(["count"])
        )
        self.inst_from_irq_values = OrderedDict()
        self.inst_from_irq_values = {Name(["none"]): Name(["unknown"])}
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


class IpHelper:
    UNNAMED_REG_BLOCK_NAME = "core"
    INST_ID_FIELD_NAME = Name(["inst", "id"])
    BASE_ADDR_FIELD_NAME = Name(["base", "addr"])
    CLOCK_FIELD_NAME = Name(["clock"])
    PERIPH_IO_FIELD_NAME = Name(["periph", "io"])
    DT_STRUCT_NAME_PREFIX = Name(["dt", "desc"])
    FIRST_IRQ_FIELD_NAME = Name(["first", "irq"])

    def __init__(self, top_helper: TopHelper, ip: IpBlock, default_node: str,
                 enum_type, array_mapping_type):
        self.top_helper = top_helper
        self.top = top_helper.top
        self.ip = ip
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
        self._init_irqs()
        self._init_clocks()
        self._init_periph_io()
        self._init_instances()

    def _init_reg_blocks(self):
        reg_blocks = []
        self._reg_block_map = {}
        for rb in self.ip.reg_blocks.keys():
            if rb is None:
                reg_blocks.append(self.UNNAMED_REG_BLOCK_NAME)
            else:
                reg_blocks.append(rb)

        assert self.default_node in reg_blocks, \
            "default node ({}) is invalid".format(self._default_node)

        self.reg_block_enum = self._enum_type(
            Name([]), Name(["dt"]) + self.ip_name + Name(["reg", "block"]))
        for rb in reg_blocks:
            self.reg_block_enum.add_constant(Name.from_snake_case(rb))
        if isinstance(self.reg_block_enum, CEnum):
            self.reg_block_enum.add_constant(Name(["count"]), "Number of register blocks")

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
            self.irq_enum.add_constant(Name(["count"]), "Number of IRQs")

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
            self.clock_enum.add_constant(Name.from_snake_case(clk))
        if isinstance(self.reg_block_enum, CEnum):
            self.clock_enum.add_constant(Name(["count"]), "Number of clock ports")

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
            self.periph_io_enum.add_constant(Name(["count"]), "Number of peripheral I/O")

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
            self.inst_enum.add_constant(inst_name)
            if self.first_inst_id is None:
                self.first_inst_id = TopHelper.DT_INSTANCE_ID_NAME + Name.from_snake_case(m["name"])
            self.last_inst_id = TopHelper.DT_INSTANCE_ID_NAME + Name.from_snake_case(m["name"])
            self.inst_dt_values[inst_name] = self._create_instance(m)
            self.inst_map[inst_name] = m
        if isinstance(self.inst_enum, CEnum):
            self.inst_enum.add_constant(Name(["count"]), "Number of instances")

    def _create_dt_struct(self):
        self.inst_struct = StructType(self.DT_STRUCT_NAME_PREFIX + self.ip_name)
        self.inst_struct.add_field(
            name = self.INST_ID_FIELD_NAME,
            field_type = ScalarType(TopHelper.DT_INSTANCE_ID_NAME),
            docstring = "Instance ID"
        )
        self.inst_struct.add_field(
            name = self.BASE_ADDR_FIELD_NAME,
            field_type = ArrayMapType(
                elem_type = ScalarType("uint32_t"),
                index_type = ScalarType(self.reg_block_enum.name),
                length = Name(["count"]),
            ),
            docstring = "Base address of each register block"
        )
        if self.has_irqs():
            # FIXME We need to handle better the case where a block is not connected to the PLIC.
            self.inst_struct.add_field(
                name = self.FIRST_IRQ_FIELD_NAME,
                field_type = ScalarType(Name(["top"]) +
                                        Name.from_snake_case(self.top["name"]) +
                                        Name(["plic", "irq", "id"])),
                docstring = """PLIC ID of the first IRQ of this instance

This can be `kDtPlicIrqIdNone` if the block is not connected to the PLIC."""
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

    def _create_instance(self, m):
        """
        Fill the description structure of an instance.
        """
        modname = m["name"]
        inst_desc = OrderedDict()
        # Instance ID.
        inst_desc[self.INST_ID_FIELD_NAME] = Name.from_snake_case(modname)
        # Base address map.
        base_addr_map = OrderedDict()
        for (rb, addr) in m["base_addrs"].items():
            if rb == "null":
                rb = self.UNNAMED_REG_BLOCK_NAME
            rb = Name.from_snake_case(rb)
            # It is possible that this module is not accessible in this
            # address space. In this case, return a dummy value.
            # FIXME Maybe find a better way of doing this.
            base_addr_map[rb] = addr.get(self._addr_space, "0xffffffff")
        inst_desc[self.BASE_ADDR_FIELD_NAME] = base_addr_map
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
        # Periph I/O
        if self.has_periph_io():
            periph_ios = OrderedDict()
            for (sig, (port, idx)) in self._device_signals.items():
                found = False
                for conn in self.top["pinmux"]["ios"]:
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
            for io in self.top['pinmux']['ios']:
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
