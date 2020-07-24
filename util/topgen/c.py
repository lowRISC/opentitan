# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate `top_{name}.h` and
`top_{name}.h`.
"""


class Name(object):
    """We often need to format names in specific ways, this class does so."""
    def __add__(self, other):
        return Name(self.parts + other.parts)

    @staticmethod
    def from_snake_case(input):
        return Name(input.split("_"))

    def __init__(self, parts):
        self.parts = list(parts)

    def as_snake_case(self):
        return "_".join([p.lower() for p in self.parts])

    def as_c_define(self):
        return "_".join([p.upper() for p in self.parts])


class MemoryRegion(object):
    def __init__(self, name, base_addr, size_bytes):
        self.name = name
        self.base_addr = base_addr
        self.size_bytes = size_bytes

    def base_addr_name(self):
        return self.name + Name(["base", "addr"])

    def size_bytes_name(self):
        return self.name + Name(["size", "bytes"])


class TopGenC(object):
    def __init__(self, top_info):
        self._top_name = Name(["top"]) + Name.from_snake_case(top_info["name"])
        self.top = top_info

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
