#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Runs coverage smoke tests with JSON expectations.

This script runs coverage tests and checks for expected coverage
status (hit, miss, or skip) for functions and lines
based on a JSON configuration.
"""

import argparse
import json
import re
import subprocess
from pathlib import Path

MERGED_REPORT = Path("bazel-out/_coverage/_coverage_report.dat")
LCOV_LIST = Path("bazel-out/_coverage/lcov_files.tmp")


def _get_func_lineno(file_path: Path, pattern: str) -> int:
    """Finds the line number for a given pattern in a file.

    Returns:
        The 1-based line number where the function is found.
    """
    file_content = file_path.read_text()
    try:
        # Find the start of the pattern.
        start_index = file_content.index(pattern)
        # Count newlines up to the end of the pattern.
        return file_content[:start_index + len(pattern)].count('\n') + 1
    except ValueError:
        raise ValueError(f"Pattern '{pattern}' not found in file {file_path}")


def _check_ans(name: str, ans: str, is_hit: bool, is_miss: bool) -> bool:
    """Compares the actual coverage status with the expected status."""
    if ans == 'hit' and is_hit:
        print(f" PASS: {name} correctly marked as {ans}.")
    elif ans == 'miss' and not is_hit and is_miss:
        print(f" PASS: {name} correctly marked as {ans}.")
    elif ans == 'skip' and not is_hit and not is_miss:
        print(f" PASS: {name} correctly marked as {ans}.")
    else:
        print(f" FAIL: {name} should be {ans}, "
              f"but is_hit={is_hit}, is_miss={is_miss}.")
        return False
    return True


def _run_smoke_test(path: Path) -> bool:
    """Runs a single smoke test defined by an expectation JSON file."""
    file_pass = True
    print(f"Smoke test with expectation file: {path}")

    with open(path, 'r') as f:
        config = json.load(f)

    for test_target in config["tests"]:
        print(f"Running bazel coverage for: {test_target}")
        print()
        cmd = [
            "./bazelisk.sh", "coverage", "--test_output=errors",
            "--config=ot_coverage", test_target
        ]
        try:
            subprocess.run(cmd, check=True)
        except subprocess.CalledProcessError as e:
            print(f"FAIL: Bazel command failed with error: {e}")
            file_pass = False
            continue
        print()

        # Check for the single coverage.dat file.
        lcov_files = LCOV_LIST.read_text().splitlines()
        lcov_files = [e for e in lcov_files if e.endswith('/coverage.dat')]
        if len(lcov_files) != 1:
            print("FAIL: Expected exactly one coverage.dat file.")
            file_pass = False
            continue
        if not Path(lcov_files[0]).is_file():
            print(f"FAIL: Coverage report {lcov_files[0]} not found.")
            file_pass = False
            continue

        # Check contents in merged report.
        if not MERGED_REPORT.is_file():
            print(f"FAIL: Coverage report {MERGED_REPORT} not found.")
            file_pass = False
            continue

        contents = MERGED_REPORT.read_text()

        for filename, coverage in config["coverage"].items():
            print(f"Checking expectations for file: {filename}")

            # Extract content for the specific file
            file_regex = fr"^SF:{re.escape(filename)}\n(.*?)^end_of_record"
            record_match = re.search(file_regex, contents, re.M | re.S)
            if not record_match:
                print(f" FAIL: No '{filename}' in coverage report.")
                file_pass = False
                continue
            record = record_match.group(1)

            # Assert function coverage (FNDA records)
            for func_name, ans in coverage['funcs'].items():
                re_pattern = fr'(?:.*:)?{re.escape(func_name)}'
                re_hit = fr"^FNDA:[1-9][0-9]*,{re_pattern}$"
                re_miss = fr"^FNDA:0,{re_pattern}$"
                name = f"Func '{func_name}'"
                is_hit = bool(re.search(re_hit, record, re.M))
                is_miss = bool(re.search(re_miss, record, re.M))
                file_pass &= _check_ans(name, ans, is_hit, is_miss)

            # Assert line coverage (DA records)
            for line_pattern, ans in coverage['lines'].items():
                lineno = _get_func_lineno(Path(filename), line_pattern)
                re_hit = fr"^DA:{lineno},[1-9][0-9]*$"
                re_miss = fr"^DA:{lineno},0$"
                name = f"Line {lineno} for '{line_pattern}'"
                is_hit = bool(re.search(re_hit, record, re.M))
                is_miss = bool(re.search(re_miss, record, re.M))
                file_pass &= _check_ans(name, ans, is_hit, is_miss)
            print()

    if not file_pass:
        print(f" FAIL: Coverage check for {path} failed.")
    print()

    return file_pass


def main() -> None:
    overall_pass = True

    parser = argparse.ArgumentParser(description="Run coverage smoke tests.")
    parser.add_argument("json_files",
                        nargs="+",
                        type=Path,
                        help="Specific JSON expectation files to run.")
    args = parser.parse_args()

    for path in args.json_files:
        overall_pass &= _run_smoke_test(path)

    if not overall_pass:
        print("FAIL: Some coverage smoke tests failed.")
        exit(1)
    else:
        print("PASS: All coverage smoke tests passed.")


if __name__ == "__main__":
    main()
