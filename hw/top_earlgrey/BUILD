# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules:autogen.bzl", "autogen_hjson_header")
load("//rules/opentitan:defs.bzl", "fpga_cw310", "sim_verilator")

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

fpga_cw310(
    name = "fpga_cw310",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ] + select({
        "@//ci:lowrisc_fpga_cw310": ["--uarts=/dev/ttyACM_CW310_1,/dev/ttyACM_CW310_0"],
        "//conditions:default": [],
    }),
    bitstream = "//hw/bitstream:test_rom",
    design = "earlgrey",
    exec_env = "fpga_cw310",
    lib = "//sw/device/lib/arch:fpga_cw310",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    param = {
        "interface": "cw310",
        "exit_success": r"PASS.*\n",
        "exit_failure": r"(FAIL|FAULT).*\n",
    },
    test_cmd = """
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw310(
    name = "fpga_cw310_rom_with_fake_keys",
    testonly = True,
    base = ":fpga_cw310",
    exec_env = "fpga_cw310_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
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
    data = [
        "//hw:fusesoc_ignore",
        "//hw:verilator",
    ],
    design = "earlgrey",
    exec_env = "sim_verilator",
    lib = "//sw/device/lib/arch:sim_verilator",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/ip/otp_ctrl/data:img_rma",
    param = {
        "exit_success": r"PASS.*\n",
        "exit_failure": r"(FAIL|FAULT).*\n",
    },
    rom = "//sw/device/lib/testing/test_rom:test_rom_sim_verilator_scr_vmem",
    test_cmd = """
        --exec="console --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)
