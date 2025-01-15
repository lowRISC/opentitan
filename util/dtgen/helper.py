# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate the device tables (DT)
files.
"""
from typing import Dict

from topgen.lib import CEnum, CArrayMapping, Name
from reggen.ip_block import IpBlock


class TopHelper:
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
        self.instance_type_enum = self._enum_type(Name([]), Name(["dt", "instance", "type"]))
        self.instance_type_enum.add_constant(Name(["unknown"]), "Instance of unknown type")
        for module_name in self._module_types:
            self.instance_type_enum.add_constant(
                Name.from_snake_case(module_name),
                f"instance of {module_name}"
            )
        if isinstance(self.instance_type_enum, CEnum):
            self.instance_type_enum.add_constant(Name(["count"]), "Number of instance types")

        # List of all module instance IDs
        self.instance_id_enum = self._enum_type(Name([]), Name(["dt", "instance", "id"]))
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
        self._init_pins()

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

    def has_pins(self):
        return len(self._device_pins) > 0

    def _init_pins(self):
        inouts, inputs, outputs = self.ip.xputs
        self._device_pins = []
        for sig in inputs + outputs + inouts:
            if sig.bits.width() > 1:
                for bit in range(sig.bits.width()):
                    self._device_pins.append(sig.name + str(bit))
            else:
                self._device_pins.append(sig.name)

        self.pin_enum = self._enum_type(Name([]), Name(["dt"]) + self.ip_name + Name(["pin"]))
        for pin in self._device_pins:
            self.pin_enum.add_constant(Name.from_snake_case(pin))
        if isinstance(self.reg_block_enum, CEnum):
            self.pin_enum.add_constant(Name(["count"]), "Number of pins")
