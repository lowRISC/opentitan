# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_library", "py_test")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "wrapper",
    srcs = [
        "wrapper.py",
    ],
)

py_test(
    name = "wrapper_test",
    srcs = [
        "wrapper_test.py",
    ],
    deps = [
        ":wrapper",
    ],
)

py_library(
    name = "ot_logging",
    srcs = [
        "ot_logging.py",
    ],
    deps = [
        requirement("rich"),
        ":wrapper",
    ],
)

py_test(
    name = "ot_logging_test",
    srcs = [
        "ot_logging_test.py",
    ],
    deps = [
        ":ot_logging",
    ],
)

py_library(
    name = "run",
    srcs = [
        "run.py",
    ],
    deps = [
        ":ot_logging",
    ],
)

py_test(
    name = "run_test",
    srcs = [
        "run_test.py",
    ],
    deps = [
        ":ot_logging",
        ":run",
    ],
)

py_library(
    name = "bazel",
    srcs = [
        "bazel.py",
    ],
    deps = [
        ":run",
    ],
)

py_test(
    name = "bazel_test",
    srcs = [
        "bazel_test.py",
    ],
    deps = [
        ":bazel",
    ],
)

py_library(
    name = "register_usage_report",
    srcs = [
        "register_usage_report.py",
    ],
    imports = [
        # Workaround for ModuleNotFoundError when attempting to import clang. It
        # seems that libclang puts the "clang" module a bit deeper in the
        # package than other pip packages, such as "rich".
        #
        # Depending on `requirement("libclang")` adds the following directory:
        #   ${runfiles}/ot_python_deps/pypi__libclang
        #
        # However, that import path is not sufficient to `import clang` because
        # the clang module is actually two levels deeper.
        "../../../../../ot_python_deps/pypi__libclang/libclang-16.0.0.data/platlib/",
    ],
    deps = [
        requirement("libclang"),
        ":ot_logging",
    ],
)

py_test(
    name = "register_usage_report_test",
    srcs = [
        "register_usage_report_test.py",
    ],
    deps = [
        ":register_usage_report",
    ],
)
