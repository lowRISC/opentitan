#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Runs, i.e. walks through, the test points of a manual test plan.

This script prints the descriptions of each test point in a manual test plan
one by one and prompts whether they pass or fail. A manual test plan passes if
all test points are interactively verified.

  Typical usage:

  # This script can be run either directly, or
  util/run_manual_tests.py sw/device/silicon_creator/rom/data/rom_manual_testplan.hjson
  # via the `manual_test()` bazel rule.
  bazel test -t- //sw/device/silicon_creator/rom:manual
"""

import os
import re
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Tuple

import hjson
import typer
from pluralizer import Pluralizer
from rich.console import Console
from rich.markdown import Markdown
from rich.prompt import Confirm
from rich.text import Text

pluralize = Pluralizer().pluralize


def _get_tty():
    """Returns the terminal that we should use.

    When this script is run directly, the terminal should be the terminal of the process.
    When this script is run by bazel, the terminal should be the terminal of the bazel
    client. Note that we cannot simply traverse the process tree, since this script is
    run by the bazel server, which could be started from a different terminal.
    """
    term = subprocess.check_output(
        ["/bin/ps", "-p", f"{os.getpid()}", "-o", "tty="]).decode().strip()
    if term == "?":
        res = subprocess.check_output(["/bin/ps", "-axo",
                                       "tty=,cmd="]).decode()
        m = re.search(r"^(?P<term>[\w/]*) *bazel.*test.*$", res, re.MULTILINE)
        if not m:
            raise RuntimeError("Could not find the terminal")
        term = m["term"]
    return f"/dev/{term}"


# Set the terminal manually since this test is interactive.
# This is really a hack since bazel does not support interactive commands.
stdin = open(_get_tty(), "r")
stdout = open(_get_tty(), "w")
console = Console(force_interactive=True, force_terminal=True, file=stdout)


def _run_manual_testpoint(testplan_name: str,
                          testpoint: Dict[str, Any]) -> Tuple[str, bool]:
    """Runs a testpoint in a manual testplan."""
    name = f"{testplan_name}/{testpoint['name']}"
    md = f"**{name}**: {testpoint['desc']}"
    console.print(Markdown(md))
    console.print("")
    prompt = Text.styled("\n> Was the test successful? [y/n]", style="bold")
    return (name,
            Confirm.ask(prompt,
                        show_choices=False,
                        console=console,
                        stream=stdin))


def _print_results(testplan_name: str, results: List[Tuple[str,
                                                           bool]]) -> None:
    """Prints the results for a testplan."""
    title = Text.assemble(
        ("Results of testplan ", "bold"),
        (f"{testplan_name}", "bold reverse"),
        (":", "bold"),
    )
    console.print("")
    console.print(title)
    console.print("")

    for testpoint, passed in results:
        line = Text.assemble(f"  {testpoint}: ",
                             ("PASSED", "bold green") if passed else
                             ("FAILED", "bold red"))
        console.print(line)
    console.print("")

    num_tests = len(results)
    num_pass = len([res[1] for res in results if res[1]])
    num_fail = num_tests - num_pass
    summary = Text.assemble(f"{num_pass} of {num_tests} tests passed. ",
                            ("All tests PASSED",
                             "bold green") if not num_fail else
                            (f"{pluralize('test', num_fail, True)} FAILED",
                             "bold white on red"))
    console.print(summary)
    raise typer.Exit(code=num_fail)


def main(testplan_path: Path):
    """Run manual tests listed in a testplan hjson file."""
    testplan = hjson.load(testplan_path.open())
    results = [
        _run_manual_testpoint(testplan['name'], t)
        for t in testplan['testpoints']
    ]
    _print_results(testplan["name"], results)


if __name__ == "__main__":
    typer.run(main)
