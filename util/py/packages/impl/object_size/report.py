# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import functools
from pathlib import Path

from rich.console import Console
from rich.progress import BarColumn, Progress, TaskProgressColumn, TextColumn
from rich.rule import Rule
from rich.table import Column, Padding, Table

from util.py.packages.impl.object_size.elf import parse_elf_file
from util.py.packages.impl.object_size.memory import parse_memory_file
from util.py.packages.impl.object_size.types import (Address, Alignment,
                                                     Memory, Section, Size)


def print_utilization_report(memories) -> None:
    rprint(Padding("[bold]Memory utilization overview:[/bold]", (1, 0, 0, 2)))
    for m in memories.values():
        used = functools.reduce(lambda acc, sym: acc + sym.size, m.symbols, 0)
        bar = Progress(TextColumn(f"[progress.description]{m.name:20}"),
                       BarColumn(complete_style="bold cyan"),
                       TaskProgressColumn(),
                       f"{Size(used)} of {Size.__str__(m)}")
        task = bar.add_task("")
        bar.advance(task, used * 100 // m.size)
        rprint(Padding(bar.get_renderable(), (0, 0, 0, 4)))


def my_table(*args, **kwargs):
    return Table(
        *args, **{
            "highlight": True,
            "row_styles": ["on bright_black", ""],
            **kwargs
        })


def print_section_report(sections: list[Section]) -> None:
    table = my_table(
        Column("Name", justify="right", style="bold yellow", no_wrap=True),
        Column("Memory", justify="center"),
        Column("Size", justify="right"),
        Column("Address", justify="left"),
        Column("Alignment", justify="right"),
        Column("Type", justify="center"),
        Column("Flags", justify="right"),
        title="[bold]Sections ASCENDING by VMA:[/bold]",
    )

    for s in sorted(sections.values(), key=lambda s: s.vma):
        table.add_row(s.name, ', '.join(s.memories), Size.__str__(s),
                      Address.__str__(s), Alignment.__str__(s), s.type_,
                      s.flags)
    rprint(Padding(table, (2, 0, 0, 2)))
def print_report(path: Path, force_color: bool = False) -> None:
    global rprint
    rprint = Console(force_terminal=force_color).print
    rprint(Padding(Rule(f"[bold]{path.name}[/bold]"), (1, 0, 0, 2)))
    rprint(Padding("[bold]Full path:[/bold]", (1, 0, 0, 2)))
    rprint(Padding(f"{path}", (0, 0, 0, 4)))
    rprint(Padding("[bold]File size:[/bold]", (1, 0, 0, 2)))
    rprint(Padding(f"{Size(path.stat().st_size)}", (0, 0, 0, 4)))
    if (path.suffixes[-1] == ".elf"):
        memories = parse_memory_file()
        sections = parse_elf_file(path, memories)
        print_utilization_report(memories)
        print_section_report(sections)
    rprint(Padding("", (2, 0, 0, 0)))
