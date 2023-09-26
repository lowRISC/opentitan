# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_hjson_header")
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_cw310",
    "sim_dv",
    "sim_verilator",
)

autogen_hjson_header(
    name = "rv_plic_regs",
    srcs = [
        "ip_autogen/rv_plic/data/rv_plic.hjson",
    ],
)

autogen_hjson_header(
    name = "alert_handler_regs",
    srcs = [
        "ip_autogen/alert_handler/data/alert_handler.hjson",
    ],
)

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/top_earlgrey/data:all_files",
        "//hw/top_earlgrey/dv/verilator:all_files",
        "//hw/top_earlgrey/ip:all_files",
        "//hw/top_earlgrey/sw:all_files",
    ],
)

###########################################################################
# FPGA CW310 Environments
###########################################################################
fpga_cw310(
    name = "fpga_cw310",
    design = "earlgrey",
    exec_env = "fpga_cw310",
    lib = "//sw/device/lib/arch:fpga_cw310",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    test_cmd = "testing-not-supported",
)

fpga_cw310(
    name = "fpga_cw310_test_rom",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ] + select({
        "@//ci:lowrisc_fpga_cw310": ["--uarts=/dev/ttyACM_CW310_1,/dev/ttyACM_CW310_0"],
        "//conditions:default": [],
    }),
    base = ":fpga_cw310",
    bitstream = "//hw/bitstream:test_rom",
    exec_env = "fpga_cw310_test_rom",
    param = {
        "interface": "cw310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    test_cmd = """
        --exec="fpga load-bitstream {bitstream}"
        --exec="transport init"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw310(
    name = "fpga_cw310_rom_with_fake_keys",
    testonly = True,
    base = ":fpga_cw310_test_rom",
    bitstream = "//hw/bitstream:rom_with_fake_keys",
    exec_env = "fpga_cw310_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
)

###########################################################################
# Sim Verilator Environments
#
# The sim_verilator_base target is only meant to be used for building ROMs
# and other items without `testonly=True`.
###########################################################################
sim_verilator(
    name = "sim_verilator_base",
    design = "earlgrey",
    exec_env = "sim_verilator",
    lib = "//sw/device/lib/arch:sim_verilator",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/ip/otp_ctrl/data:img_rma",
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
        "--verilator-flash={firmware}",
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
    rom = "//sw/device/lib/testing/test_rom:test_rom_sim_verilator_scr_vmem",
    test_cmd = """
        --exec="console --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

###########################################################################
# Sim DV Environments
#
# The sim_dv_base target is only meant to be used for building ROMs and
# other items without `testonly=True`.
###########################################################################
sim_dv(
    name = "sim_dv_base",
    design = "earlgrey",
    exec_env = "sim_dv",
    lib = "//sw/device/lib/arch:sim_dv",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/ip/otp_ctrl/data:img_rma",
)

sim_dv(
    name = "sim_dv",
    testonly = True,
    args = [
        "{dvsim_config}",
    ],
    base = ":sim_dv_base",
    data = [
        "//hw/top_earlgrey/dv:chip_sim_cfg.hjson",
    ],
    exec_env = "sim_dv",
    extract_sw_logs = "//util/device_sw_utils:extract_sw_logs_db",
    flash_scramble_tool = "//util/design:gen-flash-img",
    lib = "//sw/device/lib/arch:sim_dv",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/ip/otp_ctrl/data:img_rma",
    otp_data_perm = "//hw/ip/otp_ctrl/data:data_perm",
    otp_mmap = "//hw/ip/otp_ctrl/data:otp_ctrl_mmap.hjson",
    otp_seed = "//hw/ip/otp_ctrl/data:otp_seed",
    param = {
        "dvsim_config": "$(location //hw/top_earlgrey/dv:chip_sim_cfg.hjson)",
    },
    rom = "//sw/device/lib/testing/test_rom:test_rom_sim_dv_scr_vmem",
)
