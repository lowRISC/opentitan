# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)
load("//rules:manifest.bzl", "manifest")

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

# Note: the boot_svc commands for ownership_{activate,unlock} are tested by
# the ownership transfer tests.  These two commands are unlike the rest of
# the ownership commands in that they require a nonce, the device
# identification number and a signature, and thus require far more test
# infrastructure than the common boot_svc commands.

opentitan_test(
    name = "boot_svc_empty_test",
    srcs = ["boot_svc_empty_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV|PASS|FAIL",
        exit_success = "FinalBootLog: 2:AA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
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
    name = "boot_svc_wakeup_test",
    srcs = ["boot_svc_wakeup_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000",
        #exit_failure = "BFV|PASS|FAIL",
        #exit_success = "FinalBootLog: 2:AA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
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
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:ABA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
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
    name = "boot_svc_primary_test",
    srcs = ["boot_svc_primary_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 5:ABBBA\r\n",
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
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
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {firmware}@0x90000",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:AAA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
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

manifest({
    "name": "manifest_version_4",
    "security_version": "4",
    "identifier": hex(CONST.OWNER),
})

opentitan_binary(
    name = "min_sec_ver_4",
    testonly = True,
    srcs = ["boot_svc_min_sec_ver_test.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_hyper310_rom_ext",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = ":manifest_version_4",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_min_bl0_sec_ver",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_min_sec_ver_test",
    srcs = ["boot_svc_min_sec_ver_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {firmware}@0x10000 {min_sec_ver_4:signed_bin}@0x90000",
        binaries = {
            ":min_sec_ver_4": "min_sec_ver_4",
        },
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            --exec="fpga clear-bitstream"
            no-op
        """,
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = "//sw/device/silicon_owner:manifest",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_min_bl0_sec_ver",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)
