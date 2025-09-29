# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "sim_dv",
    "sim_verilator",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "rtl_files",
    srcs = glob(["**"]) + [
        "//hw/top_darjeeling/data:all_files",
        "//hw/top_darjeeling/dv/verilator:all_files",
        "//hw/top_darjeeling/ip:rtl_files",
        "//hw/top_darjeeling/sw:all_files",
    ],
)

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]) + [
        "//hw/top_darjeeling/ip_autogen/ac_range_check:doc_files",
        "//hw/top_darjeeling/ip_autogen/alert_handler:doc_files",
        "//hw/top_darjeeling/ip_autogen/clkmgr:doc_files",
        "//hw/top_darjeeling/ip_autogen/gpio:doc_files",
        "//hw/top_darjeeling/ip_autogen/otp_ctrl:doc_files",
        "//hw/top_darjeeling/ip_autogen/pinmux:doc_files",
        "//hw/top_darjeeling/ip_autogen/pwrmgr:doc_files",
        "//hw/top_darjeeling/ip_autogen/racl_ctrl:doc_files",
        "//hw/top_darjeeling/ip_autogen/rstmgr:doc_files",
        "//hw/top_darjeeling/ip_autogen/rv_core_ibex:doc_files",
        "//hw/top_darjeeling/ip_autogen/rv_plic:doc_files",
    ],
)

###########################################################################
# Sim Verilator Environments
#
# The sim_verilator_base target is only meant to be used for building ROMs
# and other items without `testonly=True`.
###########################################################################
sim_verilator(
    name = "sim_verilator_base",
    design = "darjeeling",
    exec_env = "sim_verilator",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_verilator",
        "//hw/top_darjeeling/sw/dt:sim_verilator",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/top_darjeeling/data/otp:img_rma",
    test_cmd = "testing-not-supported",
)

sim_verilator(
    name = "sim_verilator",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface=verilator",
        "--verilator-bin=$(rootpath //hw:verilator)",
        "--verilator-rom={rom}",
        "--verilator-otp={otp}",
        "--verilator-ctn-ram={firmware}",
    ],
    base = ":sim_verilator_base",
    data = [
        "//hw:fusesoc_ignore",
        "//hw:verilator",
    ],
    exec_env = "sim_verilator",
    param = {
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    rom = "//sw/device/lib/testing/test_rom:test_rom",
    test_cmd = """
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

###########################################################################
# Sim DV Environments
#
# The sim_dv_base target is only meant to be used for building ROMs and
# other items without `testonly=True`.
###########################################################################
# Remark: we must use a different name from earlgrey because the test point
# names are derived from the exec_env's target named
sim_dv(
    name = "sim_dv_base",
    design = "darjeeling",
    exec_env = "sim_dv",
    extract_sw_logs = "//util/device_sw_utils:extract_sw_logs_db",
    flash_scramble_tool = "//util/design:gen-flash-img",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_dv",
        "//hw/top_darjeeling/sw/dt:sim_dv",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp_mmap = "//hw/top_darjeeling/data/otp:otp_ctrl_mmap.hjson",
)

sim_dv(
    name = "sim_dv",
    testonly = True,
    base = ":sim_dv_base",
    exec_env = "sim_dv",
    rom = "//sw/device/lib/testing/test_rom:test_rom",
)
