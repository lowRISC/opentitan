# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "bit_ranges",
    srcs = ["bit_ranges.py"],
)

py_library(
    name = "bool_literal",
    srcs = ["bool_literal.py"],
)

py_library(
    name = "cache",
    srcs = ["cache.py"],
)

py_library(
    name = "check",
    srcs = ["check.py"],
)

py_library(
    name = "constants",
    srcs = ["constants.py"],
    deps = [
        ":insn_yaml",
        ":operand",
    ],
)

py_library(
    name = "control_flow",
    srcs = ["control_flow.py"],
    deps = [
        ":decode",
        ":insn_yaml",
        ":section",
    ],
)

py_library(
    name = "decode",
    srcs = ["decode.py"],
    deps = [
        ":elf",
        ":insn_yaml",
    ],
)

py_library(
    name = "elf",
    srcs = ["elf.py"],
    deps = [
        ":mem_layout",
    ],
)

py_library(
    name = "encoding",
    srcs = ["encoding.py"],
    deps = [
        ":bool_literal",
        ":encoding_scheme",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "encoding_scheme",
    srcs = ["encoding_scheme.py"],
    deps = [
        ":bit_ranges",
        ":bool_literal",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "information_flow",
    srcs = ["information_flow.py"],
    deps = [
        ":operand",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "information_flow_analysis",
    srcs = ["information_flow_analysis.py"],
    deps = [
        ":cache",
        ":constants",
        ":control_flow",
        ":decode",
        ":information_flow",
        ":insn_yaml",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "isr",
    srcs = ["isr.py"],
    deps = [
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "insn_yaml",
    srcs = ["insn_yaml.py"],
    deps = [
        ":encoding",
        ":encoding_scheme",
        ":information_flow",
        ":isr",
        ":lsu_desc",
        ":operand",
        ":syntax",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "instruction_count_range",
    srcs = ["instruction_count_range.py"],
    deps = [
        ":control_flow",
        ":decode",
    ],
)

py_library(
    name = "lsu_desc",
    srcs = ["lsu_desc.py"],
    deps = [
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "mem_layout",
    srcs = ["mem_layout.py"],
    deps = [
        ":otbn_reggen",
        "//util/reggen:reg_block",
    ],
)

py_library(
    name = "operand",
    srcs = ["operand.py"],
    deps = [
        ":encoding",
        ":encoding_scheme",
        ":isr",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "otbn_reggen",
    srcs = ["otbn_reggen.py"],
    data = ["//hw/ip/otbn/data:all_files"],
    deps = [
        "//util/reggen:ip_block",
        "//util/reggen:reg_block",
    ],
)

py_library(
    name = "reg_dump",
    srcs = ["reg_dump.py"],
)

py_library(
    name = "section",
    srcs = ["section.py"],
    deps = [
        ":decode",
        ":insn_yaml",
    ],
)

py_library(
    name = "syntax",
    srcs = ["syntax.py"],
    deps = [
        ":operand",
    ],
)

py_library(
    name = "toolchain",
    srcs = ["toolchain.py"],
)
