#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import click
from mako.template import Template
from pathlib import Path
from testplanlib.lib import Testplan

SV_SUITE_TEMPLATE = """
test_suite(
    name = "${sival_stage}_tests",
    tests = [
        % for test in test_list:
        "${test}",
        % endfor
    ]
)
"""

ALL_SUITE_TEMPLATE = """
test_suite(
    name = "regression_test_suite",
    tests = [
        # Silicon validation test suites.
        % for s in suites:
        ":${s}",
        % endfor
        # Crypto test suites.
        "//sw/device/tests/crypto:cryptolib_test_suite",
    ]
)
"""

LICENSE_HEADER = """// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
"""


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
@click.option(
    "--fields",
    "-f",
    default=None,
    type=str,
    # help="Comma separated list of fields that should be in the output",
)
def query(input_file: str, name: str, stage: str, si_stage: str, lc_state: str, fields: str | None):
    tp = Testplan.from_top(Path(input_file))
    tp = tp.filter_testpoints(
        name=name, stage=stage, si_stage=si_stage, lc_state=lc_state
    ).filter_fields(fields)
    tp.debug()


@main.command()
@click.argument(
    "input_file",
    type=click.Path(writable=True),
    # help="The top tesplan.hjson.",
)
@click.argument(
    "out_file",
    type=click.Path(writable=True),
    # help="The bazel file",
)
def export_testsuite(input_file: str, out_file: str):
    tp = Testplan.from_top(Path(input_file))
    template = Template(SV_SUITE_TEMPLATE)
    file = Path(out_file).open("w")
    file.write(LICENSE_HEADER.replace("//", "#"))
    sv_stages = tp.get_si_stage()
    for stage in sv_stages:
        filtered = tp.filter_testpoints(si_stage=stage)
        sv_tests = filtered.get_bazel()
        file.write(template.render(sival_stage=stage.lower(), test_list=sv_tests))

    all_suite = Template(ALL_SUITE_TEMPLATE)
    file.write(all_suite.render(suites=[s.lower() + "_tests" for s in sv_stages]))
    print(f"Generated {out_file}.")
