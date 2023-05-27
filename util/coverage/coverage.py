#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Measure unit test coverage of silicon creator code.

Given a directory `out_root_dir` the coverage artifacts will be saved in
`out_root_dir`/<HEAD_TIMESTAMP>-<HEAD_HASH>/unittest/`.

Typical usage:
    util/coverage/coverage_off_target.py --print-text-report
"""

from pathlib import Path, PurePath
from typing import Dict

import typer

from common import CoverageParams, CoverageType, LogLevel, artifacts_relpath, measure_coverage
from functest_coverage import PARAMS as FUNCTEST_PARAMS
from unittest_coverage import PARAMS as UNITTEST_PARAMS

app = typer.Typer(pretty_exceptions_enable=False, add_completion=False)

PARAMS: Dict[str, CoverageParams] = {
    CoverageType.UNITTEST: UNITTEST_PARAMS,
    CoverageType.FUNCTEST: FUNCTEST_PARAMS,
}


@app.command("artifacts-relpath")
def artifacts_relpath_cmd() -> None:
    """Prints the relative path for coverage artifacts.
    """
    print(artifacts_relpath())


@app.command()
def measure(
    coverage_type: CoverageType,
    out_root_dir: Path = Path("coverage"),
    log_level: LogLevel = LogLevel.NONE,
    print_text_report: bool = False,
) -> None:
    """Measures coverage of silicon creator code."""
    measure_coverage(
        log_level=log_level,
        out_dir=out_root_dir / artifacts_relpath() /
        PurePath(coverage_type.value),
        print_text_report=print_text_report,
        **PARAMS[coverage_type]._asdict(),
    )


if __name__ == "__main__":
    app()
