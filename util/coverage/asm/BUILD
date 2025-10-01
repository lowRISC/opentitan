# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary", "py_library", "py_test")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "grammar_util",
    srcs = ["grammar_util.py"],
    deps = [
        requirement("pyparsing"),
    ],
)

py_library(
    name = "grammar",
    srcs = ["grammar.py"],
    deps = [
        requirement("pyparsing"),
        ":grammar_util",
    ],
)

py_library(
    name = "parser",
    srcs = ["parser.py"],
    deps = [
        requirement("pyparsing"),
        requirement("rich"),
        ":grammar",
        ":grammar_util",
    ],
)

py_test(
    name = "parser_test",
    srcs = ["parser_test.py"],
    deps = [":parser"],
)

py_library(
    name = "basic_block",
    srcs = ["basic_block.py"],
    deps = [":parser"],
)

py_test(
    name = "basic_block_test",
    srcs = ["basic_block_test.py"],
    deps = [
        ":basic_block",
        ":parser",
    ],
)

py_binary(
    name = "instrument",
    srcs = ["instrument.py"],
    deps = [
        ":basic_block",
        ":parser",
    ],
)

py_library(
    name = "encoding",
    srcs = ["encoding.py"],
    deps = [":parser"],
)

py_binary(
    name = "generate_mapping",
    srcs = ["generate_mapping.py"],
    deps = [
        ":basic_block",
        ":encoding",
        ":parser",
    ],
)
