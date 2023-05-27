#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import subprocess
from collections import namedtuple
from enum import Enum
from pathlib import Path, PurePath
from pprint import pformat
from typing import Callable, List

# Commands used by the coverage scripts.
BAZEL: str = "./bazelisk.sh"
LLVM_PROFDATA: str = "llvm-profdata"
LLVM_COV: str = "llvm-cov"
LLD_HOST: str = "ld.lld"
LLD_TARGET: str = "/tools/riscv/bin/riscv32-unknown-elf-ld"

# Query for device libraries to be instrumented.
DEVICE_LIBS_INC: List[str] = [
    "//sw/device/silicon_creator/...",
    "//sw/device/lib/...",
]
DEVICE_LIBS_EXC: List[str] = [
    "//sw/device/lib/dif/...",
    "//sw/device/lib/testing/... ",
    "//sw/device/lib/runtime/...",
    "//sw/device/lib/crypto/...",
    "//sw/device/lib/arch/...",
    "//sw/device/lib/ujson/...",
    "//sw/device/lib/base:status",
    "//sw/device/lib/base:mmio_on_device_do_not_use_directly",
    "//sw/device/lib/base:mmio_on_host_do_not_use_directly",
    "//sw/device/silicon_creator/rom_ext/...",
    "//sw/device/silicon_creator/rom/keys/real:real",
]
DEVICE_LIBS_QUERY: str = (
    f"kind('^cc_library rule$', ({' + '.join(DEVICE_LIBS_INC)}) "
    f"- ({' + '.join(DEVICE_LIBS_EXC)}))")


class LogLevel(str, Enum):
    NONE: str = "none"
    INFO: str = "info"
    DEBUG: str = "debug"


class CoverageType(str, Enum):
    UNITTEST: str = "unit"
    FUNCTEST: str = "func"
    E2ETEST: str = "e2e"


class BazelTestType(str, Enum):
    CC_TEST: str = "cc_test"
    SH_TEST: str = "sh_test"


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
                             env=os.environ.copy(),
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             encoding='ascii',
                             errors='ignore',
                             check=True)
    except subprocess.CalledProcessError as e:
        log.error(f"stdout: {e.stdout if e.stdout else '(empty)'}")
        log.error(f"stderr: {e.stderr if e.stderr else '(empty)'}")
        raise
    log.debug(f"stdout: {res.stdout if res.stdout else '(empty)'}")
    log.debug(f"stderr: {res.stderr if res.stderr else '(empty)'}")
    return [line for line in res.stdout.splitlines() if line]


def instrument_device_libs(device_libs: List[str], config: str) -> List[str]:
    """Instrument device libraries.

    A coverage report can be created from multiple object files as long as they have
    coverage data. However, unused inline functions can trigger confusing hash-mismatch
    warnings and functions that appear in more than one object file can cause
    undercounting. This function builds the given device libraries with coverage
    instrumentation, gathers and returns their object files which can then be combined
    into a single library to avoid such problems.

    Args:
        device_libs: List of device libraries to be instrumented.
        config: Bazel configuration to use.

    Returns:
        Instrumented object files of the given device libraries.
    """
    log.info(f"libraries to be instrumented: {pformat(device_libs)}")
    run(BAZEL, "build", f"--config={config}", *device_libs)
    starlark_list = "[f.path for f in target.output_groups.compilation_outputs.to_list()]"
    obj_files = run(BAZEL, "cquery", f"--config={config}",
                    f"({' + '.join(device_libs)})", "--output=starlark",
                    f"--starlark:expr='\\n'.join({starlark_list})")
    log.info(f"object files with coverage data: {pformat(obj_files)}")
    return obj_files


def get_test_log_dirs(test_targets: List[str]) -> List[Path]:
    """Get log directories for the given test targets.

    Args:
        test_targets: Test targets.

    Returns:
        Log directories of the given test targets.
    """
    [test_log_dir_root] = run(BAZEL, "info", "bazel-testlogs")
    test_log_dirs = []
    for t in test_targets:
        # Test targets are of the form: //foo/bar:test_name. Drop the first two
        # characters and replace ':' to get a path relative to `test_log_dir_root`.
        test_log_dir = Path(test_log_dir_root) / t[2:].replace(':', '/')
        test_log_dirs.append(test_log_dir)
    return test_log_dirs


def generate_report(out_dir: Path, merged_profile: Path, merged_library: Path,
                    report_title: str, print_text_report: bool) -> None:
    """Generate a coverage report.

    This function generates a coverage report from the given merged profile and library.

    Args:
        out_dir: Path where to save the html report.
        merged_profile: Path of merged profile data.
        merged_library: Path of the merged library with coverage data.
        print_text_report: Whether to print the text report.
    """
    # Generate html coverage report.
    run(LLVM_COV, "show", "--show-line-counts", "--show-regions",
        f"--project-title={report_title}", "--format=html",
        f"--output-dir=./{out_dir}", "--instr-profile", str(merged_profile),
        str(merged_library))
    # Generate text coverage report.
    with (out_dir / "report.txt").open("w") as f:
        f.write("\n".join(
            run(LLVM_COV, "report", "--instr-profile", str(merged_profile),
                str(merged_library))))
    if print_text_report:
        print("\n".join(
            run(LLVM_COV, "report", "--use-color", "--instr-profile",
                str(merged_profile), str(merged_library))))
    print(f"Saved coverage artifacts in {out_dir}")


# Query for unit test targets
TEST_TARGETS_INC = [
    "//sw/device/silicon_creator/...",
]
TEST_TARGETS_EXC = [
    "//sw/device/silicon_creator/rom_ext/...",
    "attr(tags, '[\\[ ]dv[,\\]]', //sw/device/silicon_creator/...)",
    "attr(tags, '[\\[ ]verilator[,\\]]', //sw/device/silicon_creator/...)",
    "attr(tags, '[\\[ ]broken[,\\]]', //sw/device/silicon_creator/...)",
]


def test_targets_query(test_type: BazelTestType) -> str:
    return (f"kind('^{test_type} rule$', ({' + '.join(TEST_TARGETS_INC)})"
            f" - ({' + '.join(TEST_TARGETS_EXC)}))")


CoverageParams = namedtuple("CoverageParams", [
    "config",
    "libs_fn",
    "objs_fn",
    "test_targets_fn",
    "test_log_dirs_fn",
    "bazel_test_type",
    "report_title",
])


def measure_coverage(*, log_level: LogLevel, out_dir: Path, config: str,
                     libs_fn: Callable[[List[str]], List[str]],
                     objs_fn: Callable[[Path, List[str]], None],
                     test_targets_fn: Callable[[List[str]], List[str]],
                     test_log_dirs_fn: Callable[[List[Path]], List[Path]],
                     bazel_test_type: BazelTestType, report_title: str,
                     print_text_report: bool) -> None:
    """Measure test coverage.

    Args:
        log_level: Log level.
        out_dir: Coverage artifacts directory.
        config: Bazel configuration to use.
        libs_fn: A callable for modifying the set of device libraries if needed.
        objs_fn: A callable for modifying the set of object files if needed.
        test_targets_fn: A callable for modifying the set of tests if needed.
        test_log_dirs_fn: A callable that returns profile files for the given tests.
        bazel_test_type: Type of bazel test to search for.
        report_title: Title of the HTML report.
        print_text_report: Whether to print the text report.
    """
    if log_level != LogLevel.NONE:
        log.basicConfig(level=log.getLevelName(log_level.upper()))
    out_dir.mkdir(parents=True, exist_ok=True)
    # Create a merged library to avoid potential issues due to inline functions or
    # duplicate definitions.
    merged_library = out_dir / "merged.so"
    device_libs_all = run(
        BAZEL,
        "query",
        DEVICE_LIBS_QUERY,
    )
    device_libs = libs_fn(device_libs_all)
    obj_files = instrument_device_libs(device_libs, config)
    objs_fn(merged_library, obj_files)
    # Gather, filter, and run tests.
    test_targets_all = run(
        BAZEL,
        "query",
        test_targets_query(bazel_test_type),
    )
    test_targets = test_targets_fn(test_targets_all)
    # Instrumented ROM overflows the space allocated for ROM. `test_targets_fn` for
    # functional tests programs the FPGA with the non-instrumented test ROM and we skip
    # bitstream loading during tests.
    run(
        BAZEL,
        "coverage",
        "--define",
        "bitstream=skip",
        f"--config={config}",
        "--test_output=all",
        *test_targets,
    )
    # Merge profile data of individual tests to be able to generate a single report
    # for all targets that we are interested in.
    merged_profile = out_dir / "merged.profdata"
    test_log_dirs = get_test_log_dirs(test_targets)
    profile_files = test_log_dirs_fn(test_log_dirs)
    run(
        LLVM_PROFDATA,
        "merge",
        "--sparse",
        "--output",
        str(merged_profile),
        *[str(p) for p in profile_files],
    )
    # Generate a report from the merged profile data and the merged library.
    generate_report(out_dir, merged_profile, merged_library, report_title,
                    print_text_report)


def artifacts_relpath() -> PurePath:
    """Relative path for coverage artifacts.

    Returns:
        "<HEAD_TIMESTAMP>-<HEAD_HASH>"
    """
    [head_hash] = run("git", "rev-parse", "HEAD")
    [head_timestamp] = run("git", "show", "-s", "--format=%ct", "HEAD")
    path = PurePath(f"{head_timestamp}-{head_hash}")
    return path
