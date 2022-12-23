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

import logging as log
import subprocess
from enum import Enum
from pathlib import Path, PurePath
from pprint import pformat
from typing import List

import typer

app = typer.Typer(pretty_exceptions_enable=False, add_completion=False)

# Commands that this script uses
BAZEL = "./bazelisk.sh"
LLD = "ld.lld"
LLVM_COV = "llvm-cov"
LLVM_PROFDATA = "llvm-profdata"

# Title of the HTML coverage report
REPORT_TITLE = "OpenTitan Unit Test Coverage"


class LogLevel(str, Enum):
    none = "none"
    info = "info"
    debug = "debug"


def run(*args) -> List[str]:
    """Run the given command in a subprocess.

    Args:
        args: Command (the first parameter) and arguments (remaining arguments).

    Returns:
        Stdout lines in a list. Empty lines are filtered out.
    """
    log.debug(f"command: {' '.join(args)}")
    try:
        res = subprocess.run(args,
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             encoding="utf-8",
                             check=True)
    except subprocess.CalledProcessError as e:
        log.error(f"stdout: {e.stdout if e.stdout else '(empty)'}")
        log.error(f"stderr: {e.stderr if e.stderr else '(empty)'}")
        raise
    log.debug(f"stdout: {res.stdout if res.stdout else '(empty)'}")
    log.debug(f"stderr: {res.stderr if res.stderr else '(empty)'}")
    return [line for line in res.stdout.splitlines() if line]


def gather_and_build_libs() -> List[str]:
    """Find all device libraries that can be built on the host and build them with
    coverage instrumentation.

    Returns:
        The list of device libraries that can be built on the host.
    """
    # Query for device libraries to be instrumented.
    DEVICE_LIBS_INC = [
        "//sw/device/silicon_creator/...",
        "//sw/device/lib/...",
    ]
    DEVICE_LIBS_EXC = [
        "//sw/device/lib/dif/...",
        "//sw/device/lib/testing/... ",
        "//sw/device/lib/runtime/...",
        "//sw/device/lib/crypto/...",
        "//sw/device/lib/arch/...",
        "//sw/device/lib/ujson/...",
        "//sw/device/lib/base:hardened_status",
        "//sw/device/lib/base:status",
        "//sw/device/lib/base:mmio_on_device_do_not_use_directly",
        "//sw/device/lib/base:mmio_on_host_do_not_use_directly",
        "//sw/device/silicon_creator/rom_ext/...",
        "//sw/device/silicon_creator/rom/keys/real:real",
    ]
    DEVICE_LIBS_QUERY = (f"kind(cc_library, ({' + '.join(DEVICE_LIBS_INC)}) "
                         f"- ({' + '.join(DEVICE_LIBS_EXC)}))")

    # Gather and build all device libs that can be built on host. We handle everything in
    # a single query instead of one query per test target since each invocation incurs
    # an additional startup cost.
    device_libs_all = run(BAZEL, "query", DEVICE_LIBS_QUERY)
    device_libs_incompat = run(
        BAZEL, "cquery", DEVICE_LIBS_QUERY, "--output=starlark",
        ("--starlark:expr=target.label "
         "if 'IncompatiblePlatformProvider' in providers(target) "
         "else ''"))
    log.info(f"incompatible libraries: {pformat(device_libs_incompat)}")
    device_libs = list(set(device_libs_all) - set(device_libs_incompat))
    log.info(f"instrumented libraries: {pformat(device_libs)}")
    run(BAZEL, "build", "--config=coverage_clang", *device_libs)

    return device_libs


def create_merged_library(device_libs: List[str], merged_so: Path):
    """Create a single shared library from the given device libraries.

    A coverage report can be created from multiple object files as long as they have
    coverage data. However, unused inline functions can trigger confusing warnings and
    functions that appear in more than one object file can cause undercounting. Linking
    the object files of the sources that we are interested in into a single shared
    library avoids such problems.

    Args:
        device_libs: List of device libraries whose object files will be linked into a
        shared library.
        merged_so: Path where to write the shared library.
    """
    # Gather all the object files and link a combined shared library with all the
    # coverage data. This eliminates hash-mismatch warnings for multiple copies of
    # unused inline functions. Note that we exclude mock_*.o since they contain
    # duplicate symbols.
    obj_files = run(
        BAZEL, "cquery", f"({' + '.join(device_libs)})", "--output=starlark",
        ("--starlark:expr='\\n'.join("
         "[f.path for f in target.output_groups.compilation_outputs.to_list()]"
         ")"))
    obj_files = [
        o for o in obj_files if not PurePath(o).name.startswith("mock_")
    ]
    log.info(f"object files with coverage data: {pformat(obj_files)}")
    run(LLD, "--shared", "-o", str(merged_so), *obj_files)


def measure_unit_test_coverage(merged_profile: Path):
    """Measure unit test coverage of silicon creator code.

    This function measures unit test coverage of silicon creator and several base
    libraries and creates a merged profile.

    Args:
        merged_profile: Path where to save the merged profile.
    """
    # Query for unit test targets
    TEST_TARGETS_INC = [
        "//sw/device/silicon_creator/...",
        "//sw/device/lib/base:hardened_memory_unittest",
        "//sw/device/lib/base:math_unittest",
        "//sw/device/lib/base:math_builtins_unittest",
        "//sw/device/lib/base:memory_unittest",
    ]
    TEST_TARGETS_EXC = ["//sw/device/silicon_creator/rom_ext/..."]
    TEST_TARGETS_QUERY = (f"kind(cc_test, ({' + '.join(TEST_TARGETS_INC)}) "
                          f"- ({' + '.join(TEST_TARGETS_EXC)}))")
    # Gather and run all test targets.
    test_targets = run(BAZEL, "query", TEST_TARGETS_QUERY)
    log.info(f"test targets: {pformat(test_targets)}")
    run(BAZEL, "coverage", "--config=coverage_clang", *test_targets)
    # Merge profile data of individual tests.
    [TESTLOGS] = run(BAZEL, "info", "bazel-testlogs")
    profile_files = [
        f"{Path(TESTLOGS)}/{t[2:].replace(':', '/')}/coverage.dat"
        for t in test_targets
    ]
    run(LLVM_PROFDATA, "merge", "--sparse", "--output", str(merged_profile),
        *profile_files)


def generate_report(out_dir: Path, merged_profile: Path, merged_so: Path,
                    print_text_report: bool):
    """Generate a coverage report.

    This function generates a coverage report from the given merged profile and shared
    library.

    Args:
        out_dir: Path where to save the html report.
        merged_profile: Path of merged profile data.
        merged_so: Path of the shared library with coverage data.
        print_text_report: Whether to print the text report.
    """
    # Generate html coverage report.
    run(LLVM_COV, "show", "-show-line-counts", "-show-regions",
        f"--project-title={REPORT_TITLE}", "--format=html",
        f"--output-dir=./{out_dir}", "--instr-profile", str(merged_profile),
        str(merged_so))
    # Generate text coverage report.
    with (out_dir / "report.txt").open("w") as f:
        f.write("\n".join(
            run(LLVM_COV, "report", "--instr-profile", str(merged_profile),
                str(merged_so))))
    if print_text_report:
        print("\n".join(
            run(LLVM_COV, "report", "--use-color", "--instr-profile",
                str(merged_profile), str(merged_so))))
    print(f"Saved coverage artifacts in {out_dir}.")


def create_out_dir(out_root_dir: Path):
    """Create the directory for coverage report.

    The report will be saved in `out_root_dir`/<HEAD_TIMESTAMP>-<HEAD_HASH>/unittest/`.

    Args:
        out_root_dir: Root of the output directory.

    Returns:
        Path where to save the coverage report.
    """
    # Report artifacts are placed under `out_root_dir`/<head_timestamp>-<head_hash>/unittest/.
    [head_hash] = run("git", "rev-parse", "HEAD")
    [head_timestamp] = run("git", "show", "-s", "--format=%ct", "HEAD")
    out_dir = out_root_dir / f"{head_timestamp}-{head_hash}/unittest/"
    out_dir.mkdir(parents=True, exist_ok=True)
    return out_dir


@app.command()
def main(log_level: LogLevel = LogLevel.none,
         out_root_dir: Path = Path("coverage"),
         print_text_report: bool = False):
    """Measures unit test coverage of silicon creator code."""
    if log_level != LogLevel.none:
        log.basicConfig(level=log.getLevelName(log_level.upper()))

    out_dir = create_out_dir(out_root_dir)
    # Merged profile data path
    merged_profile = out_dir / "merged.profdata"
    # Merged shared library path with all coverage data we want
    merged_so = out_dir / "merged.so"

    # Build device libs and create a merged shared library to avoid hash-mismatch
    # warnings related to unused inline functions.
    device_libs = gather_and_build_libs()
    create_merged_library(device_libs, merged_so)
    # Coverage report is generated from merged profile data from unit tests and merged
    # coverage data from the combined shared library.
    measure_unit_test_coverage(merged_profile)
    generate_report(out_dir, merged_profile, merged_so, print_text_report)


if __name__ == "__main__":
    app()
