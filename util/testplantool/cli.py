#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import click
from pathlib import Path
from testplanlib.lib import Testplan


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


@main.command()
@click.argument(
    "input_file",
    type=click.Path(writable=True),
    # help="The top tesplan.hjson.",
)
@click.option(
    "--name",
    "-n",
    default=".*",
    type=str,
    # help="name regex",
)
@click.option(
    "--stage",
    "-s",
    default=".*",
    type=str,
    # help="dv stage regex",
)
@click.option(
    "--si-stage",
    "-i",
    default=".*",
    type=str,
    # help="SiVal stage regex",
)
@click.option(
    "--lc-state",
    "-l",
    default=".*",
    type=str,
    # help="life cycle regex",
)
def query(input_file: str, name: str, stage: str, si_stage: str, lc_state: str):
    tp = Testplan.from_top(Path(input_file))
    tp = tp.filter_testpoints(name=name, stage=stage, si_stage=si_stage, lc_state=lc_state)
    tp.debug()
