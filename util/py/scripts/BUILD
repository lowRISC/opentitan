# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")

py_binary(
    name = "object_size",
    srcs = ["object_size.py"],
    deps = [
        "//util/py/packages/impl/object_size:elf",
        "//util/py/packages/impl/object_size:memory",
        "//util/py/packages/impl/object_size:report",
        "//util/py/packages/impl/object_size:types",
        "//util/py/packages/lib:bazel",
        "//util/py/packages/lib:ot_logging",
    ],
)
