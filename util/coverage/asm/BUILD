# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary", "py_library", "py_test")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "tokenizer",
    srcs = ["tokenizer.py"],
    deps = [requirement("rich")],
)

py_test(
    name = "tokenizer_test",
    srcs = ["tokenizer_test.py"],
    deps = [":tokenizer"],
)

py_library(
    name = "basic_block",
    srcs = ["basic_block.py"],
    deps = [":tokenizer"],
)

py_test(
    name = "basic_block_test",
    srcs = ["basic_block_test.py"],
    deps = [
        ":basic_block",
        ":tokenizer",
    ],
)

py_binary(
    name = "instrument",
    srcs = ["instrument.py"],
    deps = [
        ":basic_block",
        ":tokenizer",
    ],
)

py_library(
    name = "encoding",
    srcs = ["encoding.py"],
    deps = [":tokenizer"],
)

py_binary(
    name = "generate_mapping",
    srcs = ["generate_mapping.py"],
    deps = [
        ":basic_block",
        ":encoding",
        ":tokenizer",
    ],
)
