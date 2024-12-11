# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "bit_ranges",
    srcs = ["bit_ranges.py"],
    imports = [".."],
)

py_library(
    name = "bool_literal",
    srcs = ["bool_literal.py"],
    imports = [".."],
)

py_library(
    name = "cache",
    srcs = ["cache.py"],
    imports = [".."],
)

py_library(
    name = "check",
    srcs = ["check.py"],
    imports = [".."],
)

py_library(
    name = "constants",
    srcs = ["constants.py"],
    imports = [".."],
    deps = [
        ":insn_yaml",
        ":operand",
    ],
)

py_library(
    name = "control_flow",
    srcs = ["control_flow.py"],
    imports = [".."],
    deps = [
        ":decode",
        ":insn_yaml",
        ":section",
    ],
)

py_library(
    name = "decode",
    srcs = ["decode.py"],
    imports = [".."],
    deps = [
        ":elf",
        ":insn_yaml",
    ],
)

py_library(
    name = "elf",
    srcs = ["elf.py"],
    imports = [".."],
    deps = [
        ":mem_layout",
    ],
)

py_library(
    name = "encoding",
    srcs = ["encoding.py"],
    imports = [".."],
    deps = [
        ":bool_literal",
        ":encoding_scheme",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "encoding_scheme",
    srcs = ["encoding_scheme.py"],
    imports = [".."],
    deps = [
        ":bit_ranges",
        ":bool_literal",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "information_flow",
    srcs = ["information_flow.py"],
    imports = [".."],
    deps = [
        ":operand",
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "information_flow_analysis",
    srcs = ["information_flow_analysis.py"],
    imports = [".."],
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
    imports = [".."],
    deps = [
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "insn_yaml",
    srcs = ["insn_yaml.py"],
    data = [
        "//hw/ip/otbn/data:base-insns.yml",
        "//hw/ip/otbn/data:bignum-insns.yml",
        "//hw/ip/otbn/data:csr.yml",
        "//hw/ip/otbn/data:enc-schemes.yml",
        "//hw/ip/otbn/data:insns.yml",
        "//hw/ip/otbn/data:wsr.yml",
    ],
    imports = [".."],
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
    imports = [".."],
    deps = [
        ":control_flow",
        ":decode",
    ],
)

py_library(
    name = "lsu_desc",
    srcs = ["lsu_desc.py"],
    imports = [".."],
    deps = [
        "//util/serialize:parse_helpers",
    ],
)

py_library(
    name = "mem_layout",
    srcs = ["mem_layout.py"],
    imports = [".."],
    deps = [
        ":otbn_reggen",
        "//util/reggen:reg_block",
    ],
)

py_library(
    name = "operand",
    srcs = ["operand.py"],
    imports = [".."],
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
    imports = [".."],
    deps = [
        "//util/reggen:ip_block",
        "//util/reggen:reg_block",
    ],
)

py_library(
    name = "reg_dump",
    srcs = ["reg_dump.py"],
    imports = [".."],
)

py_library(
    name = "section",
    srcs = ["section.py"],
    imports = [".."],
    deps = [
        ":decode",
        ":insn_yaml",
    ],
)

py_library(
    name = "syntax",
    srcs = ["syntax.py"],
    imports = [".."],
    deps = [
        ":operand",
    ],
)

py_library(
    name = "testgen",
    srcs = ["testgen.py"],
    imports = [".."],
)

py_library(
    name = "toolchain",
    srcs = ["toolchain.py"],
    imports = [".."],
)

py_library(
    name = "dmem_dump",
    srcs = ["dmem_dump.py"],
    imports = [".."],
)
