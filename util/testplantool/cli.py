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
)
@click.argument(
    "out",
    default="./result/top.csv",
    type=click.Path(writable=True),
)
def export_csv(input_file: str, out: str):
    """Export an OUT.csv with the testpoints found in INPUT_FILE.
    INPUT_FILE is the top testplan.hjson.
    OUT is the output filename.
    """
    Testplan.from_top(Path(input_file)).csv(Path(out))
    print("Successfully finished!")


@main.command()
@click.argument(
    "input_file",
    type=click.Path(writable=True),
)
@click.option(
    "--name",
    "-n",
    default=".*",
    type=str,
)
@click.option(
    "--stage",
    "-s",
    default=".*",
    type=str,
)
@click.option(
    "--si-stage",
    "-i",
    default=".*",
    type=str,
)
@click.option(
    "--lc-state",
    "-l",
    default=".*",
    type=str,
)
@click.option(
    "--fields",
    "-f",
    default=None,
    type=str,
)
def query(input_file: str, name: str, stage: str, si_stage: str, lc_state: str, fields: str | None):
    """Query testpoints from INPUT_FILE.hjson with filters.

    INPUT_FILE is the top testplan.hjson.
    NAME is an optional regex filter applied to the testpoint name.
    STAGE is an optional regex filter applied to the testpoint stage.
    SI-STAGE is an optional regex filter applied to the testpoint si-stage.
    LC-STATE is an optional regex filter applied to the testpoint LC-STATE.
    FIELDS is an optional comma separated list of fields that should be in the output.
    """
    tp = Testplan.from_top(Path(input_file))
    tp = tp.filter_testpoints(name=name, stage=stage, si_stage=si_stage, lc_state=lc_state)
    tp.debug()
