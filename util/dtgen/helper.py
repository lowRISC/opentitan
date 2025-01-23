# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from typing import Dict
import copy

from topgen.lib import CEnum, CArrayMapping, Name
from reggen.ip_block import IpBlock


def indent_text(text, indent):
    return "".join(indent + line for line in text.splitlines(True))


class ScalarType:
    def __init__(self, typename: object):
        self.typename = typename

    def render(self, name: Name):
        return "{} {}".format(render_type(self.typename), name.as_snake_case())


class BitFieldType:
    def __init__(self, typename: object, width: int):
        self.typename = typename
        self.width = width

    def render(self, name: Name):
        return "{} {}: {}".format(render_type(self.typename), name.as_snake_case(), self.width)


class ArrayType:
    def __init__(self, typename: object, length: Name):
        self.typename = typename
        self.length = length

    def render(self, name: Name):
        return "{} {}[{}]".format(render_type(self.typename), name.as_snake_case(),
                                  self.length.as_c_enum())


class StructType:
    def __init__(self, typename: object):
        self.typename = typename

    def render(self, name: Name):
        return "{} {}".format(self.typename.render(nested = True), name.as_snake_case())


def render_type(obj: object) -> str:
    if isinstance(obj, Name):
        return obj.as_c_type()
    elif isinstance(obj, str):
        return obj
    else:
        assert False, "I don't know how to render a {}".format(type(obj))


class Struct:
    """
    This class holds the description of a struct. It allows nesting
    of structures as well as arbitrary types.
    """

    def __init__(self, name: Name):
        self.name = name
        self.fields = []
        self.internal = False

    def mark_internal(self):
        self.internal = True

    def add_field(self, name: Name, typename: object, docstring: str = ""):
        self.fields.append((typename, name, docstring))

    def render(self, nested = False) -> str:
        if self.internal:
            copy_self = copy.copy(self)
            copy_self.internal = False
            tmp_struct = Struct(self.name)
            tmp_struct.add_field(
                name = Name(["__internal"]),
                typename = StructType(copy_self),
            )
            text = tmp_struct.render(nested = nested)
            return text

        text = ""
        for (typename, name, docstring) in self.fields:
            if len(docstring.splitlines()) > 1:
                predocstring = "/**\n{}\n */\n".format(indent_text(docstring, " * "))
                postdocstring = ""
            elif len(docstring.splitlines()) == 1:
                predocstring, postdocstring = "", " /**< {} */".format(docstring)
            else:
                predocstring, postdocstring = "", ""
            text += predocstring + typename.render(name) + ";" + postdocstring + "\n"

        text = "struct " + (self.name.as_snake_case() + " " if not nested else "") + \
            "{\n" + indent_text(text, "  ") + "}"
        if not nested:
            text = "typedef " + text + " " + self.name.as_c_type() + ";"
        return text


class TopHelper:
    DT_INSTANCE_ID_NAME = Name(["dt", "instance", "id"])
    DT_DEVICE_TYPE_NAME = Name(["dt", "device", "type"])
    DT_CLOCK_ENUM_NAME = Name(["dt", "clock"])
    DT_PAD_INDEX_NAME = Name(["dt", "pad", "index"])
    DT_PAD_NAME = Name(["dt", "pad"])
    DT_PERIPH_IO_NAME = Name(["dt", "periph", "io"])

    def __init__(self, topcfg, name_to_block: Dict[str, IpBlock], enum_type, array_mapping_type):
        self.top = topcfg
        self._top_name = Name(["top"]) + Name.from_snake_case(topcfg["name"])
        self._name_to_block = name_to_block

        assert enum_type in [CEnum], "Unsupported enum type"
        assert array_mapping_type in [CArrayMapping], \
               "Unsupported array mapping type"
        self._enum_type = enum_type
        self._array_mapping_type = array_mapping_type

        self.addr_space = "hart"

        self._module_types = sorted({m["type"] for m in topcfg["module"]})

        self._init_api()

    def _init_api(self):
        # List of all module instance types (i.e. uart, aes, etc)
        self.device_type_enum = self._enum_type(Name([]), self.DT_DEVICE_TYPE_NAME)
        self.device_type_enum.add_constant(Name(["unknown"]), "Instance of unknown type")
        for module_name in self._module_types:
            self.device_type_enum.add_constant(
                Name.from_snake_case(module_name),
                f"instance of {module_name}"
            )
        if isinstance(self.device_type_enum, CEnum):
            self.device_type_enum.add_constant(Name(["count"]), "Number of instance types")

        # List of all module instance IDs
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

        self.pad_index_enum = self._enum_type(Name([]), self.DT_PAD_INDEX_NAME)
        for pad in pads:
            name = pad['name']
            if 'width' in pad and pad['width'] > 1:
                name += str(pad['idx'])
            self.pad_index_enum.add_constant(
                Name.from_snake_case(name),
            )
        if isinstance(self.pad_index_enum, CEnum):
            self.pad_index_enum.add_constant(Name(["count"]), "Number of pads")

        # List of all clocks.
        self.clock_enum = self._enum_type(Name([]), self.DT_CLOCK_ENUM_NAME)
        clocks = self.top['clocks']
        for clock in clocks["srcs"] + clocks["derived_srcs"]:
            clock_name = Name.from_snake_case(clock["name"])
            self.clock_enum.add_constant(clock_name)
        self.clock_enum.add_constant(Name(["count"]), "Number of clocks")


class IpHelper:
    def __init__(self, ip: IpBlock, default_node: str, enum_type, array_mapping_type):
        self.ip = ip
        self.default_node = default_node
        self.ip_name = Name.from_snake_case(self.ip.name)

        assert enum_type in [CEnum], "Unsupported enum type"
        assert array_mapping_type in [CArrayMapping], \
               "Unsupported array mapping type"
        self._enum_type = enum_type
        self._array_mapping_type = array_mapping_type

        self._addr_space = "hart"
        # Name to assign to the unnamed reg block (if any)
        self.unnamed_reg_block_name = "core"
        if self.default_node is None:
            self.default_node = self.unnamed_reg_block_name

        self._init_reg_blocks()
        self._init_irqs()
        self._init_clocks()
        self._init_periph_io()
        self._init_instances()

    def _init_reg_blocks(self):
        reg_blocks = []
        for rb in self.ip.reg_blocks.keys():
            if rb is None:
                reg_blocks.append(self.unnamed_reg_block_name)
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
        device_irqs = {}
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
        for clk in self._device_clocks:
            # Remove the clk_ prefix and _i suffix of clocks.
            assert clk.startswith("clk_") and clk.endswith("_i"), \
                f"clock '{clk}' does not start with clk_ and end with _i"
            # There is a special case: if the clock name is "clk_i" then we don't want an empty name
            if clk == "clk_i":
                clk = "clk"
            else:
                clk = clk.removeprefix("clk_").removesuffix("_i")
            self.clock_enum.add_constant(Name.from_snake_case(clk))
        if isinstance(self.reg_block_enum, CEnum):
            self.clock_enum.add_constant(Name(["count"]), "Number of clock ports")

    def has_periph_io(self):
        return len(self._device_signals) > 0

    def _init_periph_io(self):
        inouts, inputs, outputs = self.ip.xputs
        self._device_signals = []
        for sig in inputs + outputs + inouts:
            if sig.bits.width() > 1:
                for bit in range(sig.bits.width()):
                    self._device_signals.append(sig.name + str(bit))
            else:
                self._device_signals.append(sig.name)

        self.periph_io_enum = self._enum_type(
            Name([]),
            Name(["dt"]) + self.ip_name + Name(["periph", "io"])
        )
        for sig in self._device_signals:
            self.periph_io_enum.add_constant(Name.from_snake_case(sig))
        if isinstance(self.reg_block_enum, CEnum):
            self.periph_io_enum.add_constant(Name(["count"]), "Number of peripheral I/O")

    def _init_instances(self):
        self.inst_struct = Struct(Name(["dt"]) + self.ip_name)
        self.inst_struct.add_field(
            name = Name(["inst", "id"]),
            typename = ScalarType(TopHelper.DT_INSTANCE_ID_NAME),
            docstring = "Instance ID"
        )
        self.inst_struct.add_field(
            name = Name(["base", "addr"]),
            typename = ArrayType(
                typename = Name(["uint32"]),
                length = self.reg_block_enum.name + Name(["count"]),
            ),
            docstring = "Base address of each register block"
        )
        if self.has_irqs():
            # FIXME We need to handle better the case where a block is not connected to the PLIC.
            self.inst_struct.add_field(
                name = Name(["first", "irq"]),
                typename = ScalarType(Name(["dt", "plic", "irq", "id"])),
                docstring = """PLIC ID of the first IRQ of this instance

This can be `kDtPlicIrqIdNone` if the block is not connected to the PLIC."""
            )
        if self.has_clocks():
            self.inst_struct.add_field(
                name = Name(["clock"]),
                typename = ArrayType(
                    typename = TopHelper.DT_CLOCK_ENUM_NAME,
                    length = self.clock_enum.name + Name(["count"]),
                ),
                docstring = "Clock signal connected to each clock port"
            )
        if self.has_periph_io():
            self.inst_struct.add_field(
                name = Name(["periph", "io"]),
                typename = ArrayType(
                    typename = TopHelper.DT_PERIPH_IO_NAME,
                    length = self.periph_io_enum.name + Name(["count"]),
                ),
                docstring = "Description of each peripheral I/O"
            )
        self.inst_struct.mark_internal()
