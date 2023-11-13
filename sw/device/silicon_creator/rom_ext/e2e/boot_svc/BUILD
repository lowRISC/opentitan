# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "boot_svc_test_lib",
    srcs = ["boot_svc_test_lib.c"],
    hdrs = ["boot_svc_test_lib.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_empty_test",
    srcs = ["boot_svc_empty_test.c"],
    cw310 = cw310_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV|PASS|FAIL",
        exit_success = "FinalBootLog: 2:AA\r\n",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = "//sw/device/silicon_owner:manifest_virtual",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_empty",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_next_test",
    srcs = ["boot_svc_next_test.c"],
    cw310 = cw310_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:ABA\r\n",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = "//sw/device/silicon_owner:manifest_virtual",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_next_boot_bl0_slot",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_bad_next_test",
    srcs = ["boot_svc_bad_next_test.c"],
    cw310 = cw310_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:AAA\r\n",
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = "//sw/device/silicon_owner:manifest_virtual",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_next_boot_bl0_slot",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)
