#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Examine the size of the ELF and binary files created by a bazel target.

Typical usage:
    python3 -m util.py.scripts.object_size <BAZEL_TARGET_NAME>

Example:
    python3 -m util.py.scripts.object_size --configs riscv32 \
        //sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310.elf
"""

import itertools

import typer
from util.py.packages.impl.object_size.report import print_report
from util.py.packages.lib import bazel
from util.py.packages.lib import ot_logging


app = typer.Typer(pretty_exceptions_enable=False, add_completion=False)

log = ot_logging.log


@app.command()
def main(target: str,
         configs: list[str] = [],
         log_level: ot_logging.LogLevel = ot_logging.LogLevel.WARNING,
         force_color: bool = False) -> None:
    ot_logging.init(log_level)

    bazel.try_escape_sandbox()

    # We use a `cc_binary` rule to produce ELF files and a `obj_transform` rule to
    # produce bin files.
    deps = [
        bazel.get_rule_deps_of_kind(target, kind)
        for kind in ["cc_binary", "obj_transform"]
    ]
    paths = []
    for dep in itertools.chain.from_iterable(deps):
        bazel.build_target(dep, configs)
        for ext in ["elf", "bin"]:
            paths += bazel.get_target_files_with_ext(dep, configs, ext)
    for path in paths:
        print_report(path, force_color)


if __name__ == "__main__":
    app()
