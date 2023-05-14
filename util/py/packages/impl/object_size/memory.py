# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
from functools import cache

from util.py.packages.impl.object_size.types import Memory


@cache
def parse_memory_file() -> dict[str, Memory]:
    # FIXME: Actually parse hw/top_earlgrey/sw/autogen/top_earlgrey_memory.ld
    memories = (
        ("rom", range(0x00008000, 0x00008000 + 0x8000)),
        ("ram_main", range(0x10000000, 0x10000000 + 0x20000)),
        ("eflash", range(0x20000000, 0x20000000 + 0x100000)),
        ("ram_ret_aon", range(0x40600000, 0x40600000 + 0x1000)),
        ("rom_ext_virtual", range(0x90000000, 0x90000000 + 0x80000)),
        ("owner_virtual", range(0xa0000000, 0xa0000000 + 0x80000)),
    )
    return {
        n: Memory(name=n,
                  vma=r.start,
                  lma="memory",
                  size=r.stop - r.start,
                  symbols=[])
        for n, r in memories
    }


def find_memory_of_addr(addr: int) -> str:
    for memory in parse_memory_file().values():
        if addr in range(memory.vma, memory.vma + memory.size):
            return memory.name
    raise ValueError(f"Could not find the memory of address {hex(addr)}")
