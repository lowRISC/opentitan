# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "constants",
    srcs = ["constants.py"],
)

py_library(
    name = "csr",
    srcs = ["csr.py"],
    deps = [
        ":flags",
        ":wsr",
    ],
)

py_library(
    name = "decode",
    srcs = ["decode.py"],
    deps = [
        ":constants",
        ":insn",
        ":isa",
        ":state",
    ],
)

py_library(
    name = "dmem",
    srcs = ["dmem.py"],
    deps = [
        ":trace",
        "//hw/ip/otbn/util/shared:mem_layout",
    ],
)

py_library(
    name = "edn_client",
    srcs = ["edn_client.py"],
)

py_library(
    name = "ext_regs",
    srcs = ["ext_regs.py"],
    deps = [
        ":edn_client",
        ":trace",
        "//hw/ip/otbn/util/shared:otbn_reggen",
        "//util/reggen:field",
        "//util/reggen:reg_block",
        "//util/reggen:register",
    ],
)

py_library(
    name = "flags",
    srcs = ["flags.py"],
    deps = [
        ":trace",
    ],
)

py_library(
    name = "gpr",
    srcs = ["gpr.py"],
    deps = [
        ":constants",
        ":reg",
    ],
)

py_library(
    name = "insn",
    srcs = ["insn.py"],
    deps = [
        ":constants",
        ":flags",
        ":isa",
        ":state",
    ],
)

py_library(
    name = "isa",
    srcs = ["isa.py"],
    deps = [
        ":state",
        "//hw/ip/otbn/util/shared:insn_yaml",
    ],
)

py_library(
    name = "load_elf",
    srcs = ["load_elf.py"],
    imports = ["../"],
    deps = [
        ":decode",
        ":sim",
        "//hw/ip/otbn/util/shared:elf",
    ],
)

py_library(
    name = "loop",
    srcs = ["loop.py"],
    deps = [
        ":constants",
        ":trace",
    ],
)

py_library(
    name = "reg",
    srcs = ["reg.py"],
    deps = [
        ":trace",
    ],
)

py_library(
    name = "sim",
    srcs = ["sim.py"],
    imports = ["../"],
    deps = [
        ":constants",
        ":decode",
        ":isa",
        ":state",
        ":stats",
        ":trace",
    ],
)

py_library(
    name = "standalonesim",
    srcs = ["standalonesim.py"],
    deps = [
        ":sim",
    ],
)

py_library(
    name = "state",
    srcs = ["state.py"],
    deps = [
        ":constants",
        ":csr",
        ":dmem",
        ":edn_client",
        ":ext_regs",
        ":flags",
        ":gpr",
        ":loop",
        ":reg",
        ":trace",
        ":wsr",
        "//hw/ip/otbn/util/shared:mem_layout",
    ],
)

py_library(
    name = "stats",
    srcs = ["stats.py"],
    deps = [
        ":insn",
        ":isa",
        ":state",
        requirement("pyelftools"),
        requirement("tabulate"),
    ],
)

py_library(
    name = "trace",
    srcs = ["trace.py"],
)

py_library(
    name = "wsr",
    srcs = ["wsr.py"],
    deps = [
        ":ext_regs",
        ":trace",
    ],
)
