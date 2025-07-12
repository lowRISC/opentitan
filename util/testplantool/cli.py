#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import click
from pathlib import Path
from testplanlib import Testplan


@click.group()
def main():
    pass


@main.command()
@click.argument(
    "input_file",
    type=click.Path(writable=True),
    # help="The top tesplan.hjson.",
)
@click.argument(
    "out",
    default="./result/top.csv",
    type=click.Path(writable=True),
    # help="The output filename.",
)
def export_csv(input_file: str, out: str):
    Testplan.from_top(Path(input_file)).csv(Path(out))
    print("Successfully finished!")
