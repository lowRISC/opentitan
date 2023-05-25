#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging
from pathlib import (
    Path,
    PurePath,
)
from pprint import pformat
from typing import List

from common import (
    BAZEL,
    DEVICE_LIBS_QUERY,
    LLD_HOST,
    BazelTestType,
    CoverageParams,
    run,
)


def handle_libs(device_libs_all: List[str]) -> List[str]:
    """Filter device libraries that are not compatible with the host.

    Args:
        device_libs_all: A list of device libraries.

    Returns:
        `device_libs_all` with incompatible libraries filtered out.
    """
    device_libs_incompat = run(
        BAZEL,
        "cquery",
        DEVICE_LIBS_QUERY,
        "--output=starlark",
        ("--starlark:expr=target.label"
         " if 'IncompatiblePlatformProvider' in providers(target)"
         " else ''"),
    )
    logging.info(f"incompatible libraries: {pformat(device_libs_incompat)}")
    return sorted(list(set(device_libs_all) - set(device_libs_incompat)))


def handle_objs(merged_library: Path, obj_files: List[str]):
    """Create a shared library from the given object files.

    This function also filters the object files of mocks.

    Args:
        merged_library: Path where to save the merged library.
        obj_files: A list of object files.
    """
    # Note that we exclude mock_*.o since they contain duplicate definitions that we
    # are not interested in.
    logging.info(f"object files with coverage data: {pformat(obj_files)}")
    run(
        LLD_HOST,
        "--shared",
        "-o",
        str(merged_library),
        *[o for o in obj_files if not PurePath(o).name.startswith("mock_")],
    )


def handle_test_targets(test_targets: List[str]) -> List[str]:
    """Add some base library tests to the given list of tests.

    Args:
        test_targets: A list of test targets.

    Returns:
        The given list of targets along with some base library tests.
    """
    res = test_targets + [
        "//sw/device/lib/base:hardened_memory_unittest",
        "//sw/device/lib/base:math_unittest",
        "//sw/device/lib/base:memory_unittest",
    ]
    logging.info(f"test targets: {pformat(res)}")
    return res


def handle_test_log_dirs(test_log_dirs: List[Path]) -> List[Path]:
    """Get coverage profiles.

    This function returns the paths of individual coverage profiles for the given list of
    test log directories.

    Args:
        test_log_dirs: A list of test log directories.

    Returns:
        Paths of individual coverage profiles.

    """
    return [d / "coverage.dat" for d in test_log_dirs]


PARAMS = CoverageParams(
    bazel_test_type=BazelTestType.CC_TEST,
    config="ot_coverage_off_target",
    libs_fn=handle_libs,
    objs_fn=handle_objs,
    test_targets_fn=handle_test_targets,
    test_log_dirs_fn=handle_test_log_dirs,
    report_title="OpenTitan Unit Test Coverage",
)
