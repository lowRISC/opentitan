# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate `top_{name}.h` and
`top_{name}.h`.
"""

from mako.template import Template


class Name(object):
    """We often need to format names in specific ways, this class does so."""
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


class TopGenC(object):
    def __init__(self, top_info):
        self.top = top_info
        self._top_name = Name(["top"]) + Name.from_snake_case(top_info["name"])

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

    def plic_targets(self):
        enum = CEnum(self._top_name + Name(["plic", "target"]))

        for core_id in range(int(self.top["num_cores"])):
            enum.add_constant(Name(["ibex", str(core_id)]),
                              docstring="Ibex Core {}".format(core_id))

        enum.add_last_constant("Final PLIC target")

        return enum
