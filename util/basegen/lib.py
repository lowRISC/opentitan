# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List


class Name:
    """
    We often need to format names in specific ways; this class does so.

    To simplify parsing and reassembling of name strings, this class
    stores the name parts as a canonical list of strings internally
    (in self._parts). The content of a name cannot be changed once it is
    created.

    The "from_*" functions parse and split a name string into the canonical
    list, whereas the "as_*" functions reassemble the canonical list in the
    format specified.

    For example, ex = Name.from_snake_case("example_name") gets split into
    ["example", "name"] internally, and ex.as_camel_case() reassembles this
    internal representation into "ExampleName".
    """

    def __add__(self, other) -> str:
        return Name(self._parts + other._parts)

    def __repr__(self) -> str:
        return "Name({})".format(self._parts)

    def __hash__(self):
        return hash(self._parts)

    def __eq__(self, other) -> bool:
        return self._parts == other._parts

    @staticmethod
    def from_snake_case(input: str) -> 'Name':
        return Name(input.split("_"))

    @staticmethod
    def to_camel_case(input: str) -> str:
        return Name.from_snake_case(input).as_camel_case()

    def __init__(self, parts: List[str]):
        self._parts = tuple(parts)
        for p in parts:
            assert len(p) > 0, "cannot add zero-length name piece"

    def as_snake_case(self) -> str:
        return "_".join([p.lower() for p in self._parts])

    def as_camel_case(self) -> str:
        out = ""
        for p in self._parts:
            # If we're about to join two parts which would introduce adjacent
            # numbers, put an underscore between them.
            if out[-1:].isnumeric() and p[:1].isnumeric():
                out += "_" + p
            else:
                out += p.capitalize()
        return out

    def as_c_define(self) -> str:
        return "_".join([p.upper() for p in self._parts])

    def as_c_enum(self) -> str:
        return "k" + self.as_camel_case()

    def as_c_type(self) -> str:
        return self.as_snake_case() + "_t"

    def as_rust_type(self) -> str:
        return self.as_camel_case()

    def as_rust_const(self) -> str:
        return "_".join([p.upper() for p in self._parts])

    def as_rust_enum(self) -> str:
        return self.as_camel_case()

    def as_sv_define(self) -> str:
        return "_".join([p.upper() for p in self._parts])

    def as_sv_enum(self) -> str:
        return self.as_camel_case()

    def as_sv_type(self) -> str:
        return self.as_snake_case() + "_t"

    def remove_part(self, part_to_remove: str) -> "Name":
        return Name([p for p in self._parts if p != part_to_remove])
