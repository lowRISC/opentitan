# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import functools
from pathlib import Path

from rich import print as rprint
from rich.padding import Padding
from rich.progress import BarColumn, Progress, TaskProgressColumn, TextColumn

from util.py.packages.impl.object_size.elf import parse_elf_file
from util.py.packages.impl.object_size.memory import parse_memory_file
from util.py.packages.impl.object_size.types import Size


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


def print_report(path: Path) -> None:
    rprint(
        Padding(
            f"[bold underline white on gray15]{path.name}:[/bold underline white on gray15]",
            (1, 0, 0, 0)))
    rprint(Padding("[bold]Full path:[/bold]", (1, 0, 0, 2)))
    rprint(Padding(f"{path}", (0, 0, 0, 4)))
    rprint(Padding("[bold]File size:[/bold]", (1, 0, 0, 2)))
    rprint(Padding(f"{Size(path.stat().st_size)}", (0, 0, 0, 4)))
    if (path.suffixes[-1] == ".elf"):
        memories = parse_memory_file()
        parse_elf_file(path, memories)
        print_utilization_report(memories)
    rprint(Padding("", (2, 0, 0, 0)))
