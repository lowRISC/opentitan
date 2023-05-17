# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Note: Names of all classes defined below should end with "Mixin" which we omit for
# brevity.

import json
from dataclasses import asdict, dataclass
from pathlib import PurePath
from typing import Union

from rich.highlighter import JSONHighlighter
from rich.text import Text


# mypy does not recognize aliases of dataclasses.dataclass, hence we cannot use
# `functools.partial` here. See
# https://mypy.readthedocs.io/en/stable/additional_features.html#caveats-known-issues
@dataclass(frozen=True)
class Item:
    """Mixin that provides helper methods for all kinds of items.
    """

    def to_dict(self) -> dict:
        """Converts the instance to a dictionary."""
        return asdict(self)

    def to_json(self) -> str:
        """Returns the json representation of the instance as a string."""
        return json.dumps(self.to_dict(), indent=4, ensure_ascii=True)

    def __rich__(self) -> Text:
        text = Text(str(self))
        JSONHighlighter().highlight(text)
        return text


@dataclass(frozen=True)
class Name(Item):
    """Mixin for all items with names.

    Attrs:
        name: Name
    """
    name: str


@dataclass(frozen=True)
class Address(Item):
    """Mixin for items with addresses.

    Attrs:
        address: Byte address.
    """
    vma: int
    lma: Union[int, str]

    def __str__(self) -> str:
        """Returns the string representation of the address of this item.
        """
        lma_str = f"{self.lma:08x}" if isinstance(self.lma,
                                                  int) else f"N/A ({self.lma})"
        return f"VMA: {self.vma:08x}, LMA: {lma_str}"


@dataclass(frozen=True)
class Size(Item):
    """Mixin for items with sizes.

    Attrs:
        size: Size in bytes
    """
    size: int

    def __str__(self) -> str:
        """Returns the string representation of the size of this item.
        """
        return f"{self.size} bytes ({self.size / 1024:.1f} KiB)"


@dataclass(frozen=True)
class Alignment(Item):
    """Mixin for alignment.

    Attrs:
        alignment: Alignment in bytes
    """
    alignment: int

    def __str__(self) -> str:
        """Returns the string representation of the alignment of this item.
        """
        return f"{self.alignment} bytes"


@dataclass(frozen=True)
class Location(Item):
    """Mixin for items with locations.

    Attr:
        file_: Path to the file where this symbol is defined
        line: Line number
    """
    file_: PurePath
    line: int

    def __str__(self) -> str:
        return f"{self.file_}:{self.line}"


@dataclass(frozen=True)
class AddressRange(Name, Address, Size, Item):
    """An address range.

    Attributes:
        name:
        address:
        size:
    """

    def contains(self, other) -> bool:
        """Checks whether the given range is completely in this memory

        Arguments:
            address:
            size:

        Returns:
            Whether the given range lies completely in this memory.

        Raises:
            RuntimeError if the given range overlaps with this memory but is not
            completely in it.
        """
        memory_range = range(self.vma, self.vma + self.size)
        start = other.vma in memory_range
        end = (other.vma + other.size - 1) in memory_range
        if start ^ end:
            raise RuntimeError(
                "Given range overlaps but is not fully inside this memory")
        return start and end


@dataclass(frozen=True)
class Symbol(AddressRange, Name, Location, Item):
    """A symbol.

    Attributes:
        name:
        vma:
        lma:
        size:
        file_:
        line:
    """
    section: str
    type_: str
    binding: str
    visibility: str

    def __str__(self):
        return (f"{self.name} ({self.section}, {Size.__str__(self)}, "
                "{Address.__str__(self)}, {self.type_}, {self.binding}, "
                "{self.visibility}, {Location.__str__(self)})")


@dataclass(frozen=True)
class Section(AddressRange, Alignment):
    memories: list[str]
    type_: str
    flags: str
    symbols: list[Symbol]


@dataclass(frozen=True)
class Memory(AddressRange, Name):
    symbols: list[Symbol]
