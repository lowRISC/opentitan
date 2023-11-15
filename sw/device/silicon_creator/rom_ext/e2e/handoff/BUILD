# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:defs.bzl", "cw310_params", "opentitan_test")

package(default_visibility = ["//visibility:public"])

ld_library(
    name = "ld_common",
    includes = ["fault_common.ld"],
    deps = [
        "//sw/device:info_sections",
        "//sw/device/silicon_creator/lib/base:static_critical_sections",
    ],
)

ld_library(
    name = "ld_slot_a",
    script = "fault_slot_a.ld",
    deps = [
        ":ld_common",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey_memory",
    ],
)

_FAULT_TEST_CASES = {
    "none": {
        "defines": ["NO_FAULT=1"],
        "exit_success": "PASS!",
    },
    "load_access": {
        "defines": ["LOAD_ACCESS_FAULT=1"],
        "exit_success": "BFV:05524902",
    },
    "store_access": {
        "defines": ["STORE_ACCESS_FAULT=1"],
        "exit_success": "BFV:07524902",
    },
    "illegal_instruction": {
        "defines": ["ILLEGAL_INSTRUCTION_FAULT=1"],
        "exit_success": "BFV:02524902",
    },
    "hardware_interrupt": {
        "defines": ["HARDWARE_INTERRUPT=1"],
        "exit_success": "BFV:8b524902",
    },
}

[
    opentitan_test(
        name = "fault_{}".format(name),
        srcs = [
            "fault_start.S",
            "fault_test.c",
        ],
        cw310 = cw310_params(
            exit_success = test_data["exit_success"],
        ),
        defines = test_data["defines"],
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        linker_script = ":ld_slot_a",
        manifest = "//sw/device/silicon_owner:manifest_standard",
        deps = [
            "//hw/ip/uart/data:uart_regs",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:bitfield",
            "//sw/device/lib/base:hardened",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/crt",
            "//sw/device/lib/dif:rv_plic",
            "//sw/device/lib/runtime:irq",
            "//sw/device/silicon_creator/lib:dbg_print",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/lib/base:static_critical",
        ],
    )
    for name, test_data in _FAULT_TEST_CASES.items()
]

test_suite(
    name = "faults",
    tests = ["fault_{}".format(name) for name in _FAULT_TEST_CASES],
)
