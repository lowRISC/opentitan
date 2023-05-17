# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import functools
from pathlib import Path
from typing import Callable, Union

from rich.console import Console
from rich.progress import BarColumn, Progress, TaskProgressColumn, TextColumn
from rich.rule import Rule
from rich.table import Column, Padding, Table

from util.py.packages.impl.object_size.elf import parse_elf_file
from util.py.packages.impl.object_size.memory import parse_memory_file
from util.py.packages.impl.object_size.types import (Address, Alignment,
                                                     Memory, Section, Size)
from util.py.packages.lib.ot_logging import log


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


def print_symbol_table(container: Union[Memory, Section], key_fn: Callable,
                       key_name: str, reverse: bool) -> None:
    symbols = container.symbols
    if not symbols:
        log.info(f"{container.name} has no symbols")
    total = 0
    table = my_table(
        Column("Name", justify="right"),
        Column("Size", justify="right"),
        Column("Section"),
        Column("Address", justify="center"),
        Column("Type", justify="center"),
        Column("Binding", justify="center"),
        Column("Visibility", justify="center"),
        title=f"[bold]Symbols in [white]{container.name}[/white] "
        f"{'DESCENDING' if reverse else 'ASCENDING'} by {key_name.upper()}:[/bold]"
    )
    symbols = sorted(symbols, key=key_fn, reverse=reverse)
    for s in symbols:
        table.add_row(s.name, f"{Size.__str__(s)}", s.section,
                      f"{Address.__str__(s)}", s.type_, s.binding,
                      s.visibility)
        total += s.size
    rprint(Padding(table, (2, 0, 0, 2)))
    rprint(Padding(f"[bold white]TOTAL: {Size(total)}[/]", (0, 0, 0, 6)))


def print_symbols_report(memories: list[Memory],
                         sections: list[Section]) -> None:

    def size(s):
        return s.size

    def vma(s):
        return s.vma

    rprint(
        Padding(Rule("[bold]Symbols Grouped by Memory[/bold]"), (1, 0, 0, 2)))
    for m in memories.values():
        print_symbol_table(m, size, "size", True)
        print_symbol_table(m, vma, "vma", False)
    rprint(
        Padding(Rule("[bold]Symbols Grouped by Section[/bold]"), (1, 0, 0, 2)))
    for s in sections.values():
        print_symbol_table(s, size, "size", True)
        print_symbol_table(s, vma, "vma", False)


def print_alignment_overhead_report(memories: list[Memory]) -> None:
    for m in memories.values():
        if not m.symbols:
            log.info(f"Skipping memory {m.name}: no symbols")
            continue
        total = 0
        expected_start = m.vma
        symbols = sorted(m.symbols, key=lambda s: s.vma)
        rows = []
        for s in symbols:
            if s.vma > expected_start:
                overhead = s.vma - expected_start
                total += overhead
                rows.append((s, expected_start, overhead))
            expected_start = s.vma + s.size
        table = my_table(
            Column("Symbol", justify="right"),
            Column("Overhead", justify="right"),
            Column("Expected VMA", justify="center"),
            Column("Actual VMA", justify="center"),
            title=f"[bold][white]{m.name.upper()}[/white] "
            "Alignment Overhead (Includes False Positives)[/bold]")
        for (s, expected_start, overhead) in sorted(rows,
                                                    key=lambda r: r[2],
                                                    reverse=True):
            table.add_row(f"{s.name}", f"{Size(overhead)}",
                          f"0x{expected_start:08x}", f"0x{s.vma:08x}")
        rprint(Padding(table, (2, 0, 0, 2)))
        rprint(Padding(f"[bold white]TOTAL:[/] {Size(total)}", (0, 0, 0, 6)))


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
        print_symbols_report(memories, sections)
        print_alignment_overhead_report(memories)

    rprint(Padding("", (2, 0, 0, 0)))
