#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
from pathlib import Path, PurePath
from typing import Any

from bs4 import BeautifulSoup
from common import (LLVM_COV, LLVM_PROFDATA, CoverageType, LogLevel,
                    artifacts_relpath, run)


def add_test_type_to_combined_report(out_root_dir: Path = Path("coverage")) -> None:
    """Adds the "Test Type" column to the combined report HTML report.

    This new column contains links to the actual coverage reports that cover each line.
    """
    combined = out_root_dir / artifacts_relpath() / "combined" / "coverage"
    func = out_root_dir / artifacts_relpath() / "func" / "coverage"
    unit = out_root_dir / artifacts_relpath() / "unit" / "coverage"

    def covered_rows(path: Path):
        """Returns the rows of a coverage report that are covered by tests."""

        def second_col_non_zero(row: Any) -> bool:
            """Return True if the second column is non-zero."""
            if row.name == 'tr':
                cols = row.find_all('td')
                return len(cols) > 1 and cols[1].getText().strip().lower(
                ) not in ["0", "", "count"]
            return False

        return BeautifulSoup(path.read_text(),
                             "html.parser").find_all(second_col_non_zero)

    def add_back_link(target_row, combined_rows, string: str, relpath) -> None:
        """Adds a link that points to `target_row` to the corresponding row in
        `combined_rows`."""
        link_in_target = target_row.contents[0].contents[0]
        line_num = int(link_in_target.string)
        pre = combined_html.new_tag("pre")
        pre.append(string)
        link_to_target = combined_html.new_tag("a",
                                               href=relpath +
                                               link_in_target["href"])
        link_to_target.append(pre)
        cell = combined_rows[line_num].contents[1]
        if cell.contents:
            span = combined_html.new_tag("span")
            span.append(" ")
            cell.append(span)
        cell.append(link_to_target)

    for combined_file in combined.rglob("*.html"):
        relpath = combined_file.relative_to(combined)
        combined_html = BeautifulSoup(combined_file.read_text(), "html.parser")
        # Skip the first row in the table which is the path of the source file.
        combined_rows = combined_html.find("table",
                                           recursive=True).contents[1:]
        # Add the column to the header row and subsequent rows.
        header_cell = combined_html.new_tag("td", style="text-align: center;")
        header_pre = combined_html.new_tag("pre")
        header_pre.append("Test Type")
        header_cell.append(header_pre)
        combined_rows[0].insert(1, header_cell)
        for row in combined_rows[1:]:
            row.insert(
                1, combined_html.new_tag("td", style="text-align: center;"))
        # Add links to functional test report.
        func_file = func / relpath
        if func_file.exists():
            for row in covered_rows(func_file):
                add_back_link(
                    row, combined_rows, "func",
                    os.path.relpath(func_file, start=combined_file.parent))
        # Add links to unit test report.
        unit_file = unit / relpath
        if unit_file.exists():
            for row in covered_rows(unit_file):
                add_back_link(
                    row, combined_rows, "unit",
                    os.path.relpath(unit_file, start=combined_file.parent))
        # Write changes.
        combined_file.write_text(str(combined_html))


def combined_report(out_root_dir: Path = Path("coverage"),
                    log_level: LogLevel = LogLevel.NONE,
                    print_text_report: bool = False) -> None:
    """Generates a combined coverage report from functional and unit test coverage
    reports.
    """
    if log_level != LogLevel.NONE:
        log.basicConfig(level=log.getLevelName(log_level.upper()))
    out_dir = out_root_dir / artifacts_relpath() / "combined"
    out_dir.mkdir(parents=False, exist_ok=True)
    merged_profile = out_dir / "merged.profdata"
    # Merge functional and unit test profile data.
    coverage_paths = [
        out_root_dir / artifacts_relpath() / PurePath(c.value)
        for c in [CoverageType.FUNCTEST, CoverageType.UNITTEST]
    ]
    libraries = [str(p / "merged.so") for p in coverage_paths]
    profiles = [str(p / "merged.profdata") for p in coverage_paths]
    run(LLVM_PROFDATA, "merge", "--sparse", "--output", str(merged_profile),
        *profiles)
    # Generate html coverage report.
    run(LLVM_COV, "show", "--show-line-counts", "--show-regions",
        "--project-title=OpenTitan Combined Coverage Report",
        "--format=html", f"--output-dir=./{out_dir}", "--instr-profile",
        str(merged_profile), libraries[0], f"--object={libraries[1]}")
    add_test_type_to_combined_report(out_root_dir)
    # Generate text coverage report.
    with (out_dir / "report.txt").open("w") as f:
        f.write("\n".join(
            run(LLVM_COV, "report", "--instr-profile", str(merged_profile),
                libraries[0], f"--object={libraries[1]}")))
    if print_text_report:
        print("\n".join(
            run(LLVM_COV, "report", "--use-color", "--instr-profile",
                str(merged_profile), libraries[0],
                f"--object={libraries[1]}")))
    print(f"Saved coverage artifacts in {out_dir}")
