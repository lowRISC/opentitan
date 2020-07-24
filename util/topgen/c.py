# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate `top_{name}.h` and
`top_{name}.h`.
"""

from collections import OrderedDict

from mako.template import Template


class Name(object):
    """We often need to format names in specific ways; this class does so."""
    def __add__(self, other):
        return Name(self.parts + other.parts)

    @staticmethod
    def from_snake_case(input):
        return Name(input.split("_"))

    def __init__(self, parts):
        self.parts = list(parts)
        for p in parts:
            assert len(p) > 0, "cannot add zero-length name piece"

    def as_snake_case(self):
        return "_".join([p.lower() for p in self.parts])

    def as_camel_case(self):
        out = ""
        for p in self.parts:
            # If we're about to join two parts which would introduce adjacent
            # numbers, put an underscore between them.
            if out[-1:].isnumeric() and p[:1].isnumeric():
                out += "_" + p
            else:
                out += p.capitalize()
        return out

    def as_c_define(self):
        return "_".join([p.upper() for p in self.parts])

    def as_c_enum(self):
        return "k" + self.as_camel_case()

    def as_c_type(self):
        return self.as_snake_case() + "_t"


class MemoryRegion(object):
    def __init__(self, name, base_addr, size_bytes):
        self.name = name
        self.base_addr = base_addr
        self.size_bytes = size_bytes

    def base_addr_name(self):
        return self.name + Name(["base", "addr"])

    def size_bytes_name(self):
        return self.name + Name(["size", "bytes"])


class CEnum(object):
    def __init__(self, name):
        self.name = name
        self.enum_counter = 0
        self.finalized = False

        self.constants = []

    def add_constant(self, constant_name, docstring=""):
        assert not self.finalized

        full_name = self.name + constant_name

        value = self.enum_counter
        self.enum_counter += 1

        self.constants.append((full_name, value, docstring))

        return full_name

    def add_last_constant(self, docstring=""):
        assert not self.finalized

        full_name = self.name + Name(["last"])

        _, last_val, _ = self.constants[-1]

        self.constants.append((full_name, last_val, r"\internal " + docstring))
        self.finalized = True

    def render(self):
        template = ("typedef enum ${enum.name.as_snake_case()} {\n"
                    "% for name, value, docstring in enum.constants:\n"
                    "  ${name.as_c_enum()} = ${value}, /**< ${docstring} */\n"
                    "% endfor\n"
                    "} ${enum.name.as_c_type()};")
        return Template(template).render(enum=self)


class CArrayMapping(object):
    def __init__(self, name, output_type_name):
        self.name = name
        self.output_type_name = output_type_name

        self.mapping = OrderedDict()

    def add_entry(self, in_name, out_name):
        self.mapping[in_name] = out_name

    def render_declaration(self):
        template = (
            "extern const ${mapping.output_type_name.as_c_type()}\n"
            "    ${mapping.name.as_snake_case()}[${len(mapping.mapping)}];")
        return Template(template).render(mapping=self)

    def render_definition(self):
        template = (
            "const ${mapping.output_type_name.as_c_type()}\n"
            "    ${mapping.name.as_snake_case()}[${len(mapping.mapping)}] = {\n"
            "% for in_name, out_name in mapping.mapping.items():\n"
            "  [${in_name.as_c_enum()}] = ${out_name.as_c_enum()},\n"
            "% endfor\n"
            "};\n")
        return Template(template).render(mapping=self)


class TopGenC(object):
    def __init__(self, top_info):
        self.top = top_info
        self._top_name = Name(["top"]) + Name.from_snake_case(top_info["name"])

        # The .c file needs the .h file's relative path, store it here
        self.header_path = None

        self._init_plic_targets()
        self._init_plic_mapping()

    def _init_plic_targets(self):
        enum = CEnum(self._top_name + Name(["plic", "target"]))

        for core_id in range(int(self.top["num_cores"])):
            enum.add_constant(Name(["ibex", str(core_id)]),
                              docstring="Ibex Core {}".format(core_id))

        enum.add_last_constant("Final PLIC target")

        self.plic_targets = enum

    def _init_plic_mapping(self):
        """We eventually want to generate a mapping from interrupt id to the
        source peripheral.

        In order to do so, we generate two enums, and store the generated names
        in a dictionary that represents the mapping.

        Plic Interrupt ID 0 corresponds to no interrupt, and so no peripheral,
        so we encode that in the enum as "unknown".

        The interrupts have to be added in order, with "none" first, to ensure
        that they get the correct mapping to their PLIC id, which is used for
        addressing the right registers and bits.
        """
        sources = CEnum(self._top_name + Name(["plic", "peripheral"]))
        interrupts = CEnum(self._top_name + Name(["plic", "irq", "id"]))
        plic_mapping = CArrayMapping(
            self._top_name + Name(["plic", "interrupt", "for", "peripheral"]),
            sources.name)

        unknown_source = sources.add_constant(Name(["unknown"]),
                                              docstring="Unknown Peripheral")
        none_irq_id = interrupts.add_constant(Name(["none"]),
                                              docstring="No Interrupt")
        plic_mapping.add_entry(none_irq_id, unknown_source)

        # When we generate the `interrupts` enum, the only info we have about
        # the source is the module name. We'll use `source_name_map` to map a
        # short module name to the full name object used for the enum constant.
        source_name_map = {}

        for name in self.top["interrupt_module"]:
            source_name = sources.add_constant(Name.from_snake_case(name),
                                               docstring=name)
            source_name_map[name] = source_name

        sources.add_last_constant("Final PLIC peripheral")

        for intr in self.top["interrupt"]:
            # Some interrupts are multiple bits wide. Here we deal with that by
            # adding a bit-index suffix
            if "width" in intr and int(intr["width"]) != 1:
                for i in range(int(intr["width"])):
                    name = Name.from_snake_case(
                        intr["name"]) + Name([str(i)])
                    irq_id = interrupts.add_constant(name,
                                                     docstring="{} {}".format(
                                                         intr["name"], i))
                    source_name = source_name_map[intr["module_name"]]
                    plic_mapping.add_entry(irq_id, source_name)
            else:
                name = Name.from_snake_case(intr["name"])
                irq_id = interrupts.add_constant(name, docstring=intr["name"])
                source_name = source_name_map[intr["module_name"]]
                plic_mapping.add_entry(irq_id, source_name)

        interrupts.add_last_constant("The Last Valid Interrupt ID.")

        self.plic_sources = sources
        self.plic_interrupts = interrupts
        self.plic_mapping = plic_mapping

    def modules(self):
        return [(m["name"],
                 MemoryRegion(self._top_name + Name.from_snake_case(m["name"]),
                              m["base_addr"], m["size"]))
                for m in self.top["module"]]

    def memories(self):
        return [(m["name"],
                 MemoryRegion(self._top_name + Name.from_snake_case(m["name"]),
                              m["base_addr"], m["size"]))
                for m in self.top["memory"]]
