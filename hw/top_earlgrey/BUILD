# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_hjson_header")
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_cw305",
    "fpga_cw310",
    "fpga_cw340",
    "sim_dv",
    "sim_verilator",
)

package(default_visibility = ["//visibility:public"])

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
    rom_scramble_config = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
    test_cmd = "testing-not-supported",
)

fpga_cw310(
    name = "fpga_cw310_test_rom",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ],
    base = ":fpga_cw310",
    bitstream = "//hw/bitstream/hyperdebug:test_rom",
    exec_env = "fpga_cw310_test_rom",
    param = {
        "interface": "hyper310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    test_cmd = """
        --exec="transport init"
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw310(
    name = "fpga_cw310_rom_with_fake_keys",
    testonly = True,
    base = ":fpga_cw310_test_rom",
    bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
    exec_env = "fpga_cw310_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest_standard",
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:test_private_key_0": "test_key_0"},
)

fpga_cw310(
    name = "fpga_cw310_rom_ext",
    testonly = True,
    base = ":fpga_cw310_test_rom",
    bitstream = "//hw/bitstream/hyperdebug:rom_with_fake_keys",
    exec_env = "fpga_cw310_rom_ext",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    manifest = "//sw/device/silicon_owner:manifest_standard",
    param = {
        "interface": "hyper310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "assemble": "{rom_ext}@0 {firmware}@0x10000",
    },
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
    rsa_key = {"//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_test_private_key_0": "test_key_0"},
)

# FPGA configuration used to emulate silicon targets. This rule can be used by
# targets that require executing at the `rom_ext` stage level in flash, as well
# as SRAM programs. Use the `fpga_cw310_sival_rom_ext` execution environment to
# emulate silicon targets containing a `rom_ext` stage.
fpga_cw310(
    name = "fpga_cw310_sival",
    testonly = True,
    base = ":fpga_cw310_rom_with_fake_keys",
    bitstream = "//hw/bitstream:rom_with_fake_keys_otp_sival_prod_personalized",
    exec_env = "fpga_cw310_sival",

    # PROD keys are allowed to run across all life cycle stages. This prod key
    # is used to enable execution across life cycle stages with a single
    # binary.
    rsa_key = {"//sw/device/silicon_creator/rom/keys/fake/rsa:prod_private_key_0": "prod_key_0"},
)

# FPGA configuration used to emulate silicon targets containing a `rom_ext`
# stage. See `fpga_cw310_sival` for more details.
fpga_cw310(
    name = "fpga_cw310_sival_rom_ext",
    testonly = True,
    base = ":fpga_cw310_rom_ext",
    bitstream = "//hw/bitstream:rom_with_fake_keys_otp_sival_prod_personalized",
    exec_env = "fpga_cw310_sival_rom_ext",
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_sival_prod_signed_slot_a",
    rsa_key = {"//sw/device/silicon_creator/rom_ext/keys/fake:rom_ext_prod_private_key_0": "prod_key_0"},
)

###########################################################################
# FPGA CW305 Environments
#
# TODO(opentitan#19493): Determine whether the `fpga_cw310` infrastructure
# should become a more generic `fpga_chipwhisperer` infrastruture able to
# handle multiple CW-type boards.
###########################################################################
fpga_cw305(
    name = "fpga_cw305",
    design = "earlgrey",
    exec_env = "fpga_cw305",
    lib = "//sw/device/lib/arch:fpga_cw305",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rom_scramble_config = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
    test_cmd = "testing-not-supported",
)

###########################################################################
# FPGA CW340 Environments
#
# TODO(opentitan#19493): Determine whether the `fpga_cw310` infrastructure
# should become a more generic `fpga_chipwhisperer` infrastruture able to
# handle multiple CW-type boards.
###########################################################################
fpga_cw340(
    name = "fpga_cw340",
    design = "earlgrey",
    exec_env = "fpga_cw340",
    lib = "//sw/device/lib/arch:fpga_cw340",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rom_scramble_config = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
    test_cmd = "testing-not-supported",
)

fpga_cw340(
    name = "fpga_cw340_test_rom",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ] + select({
        "@//ci:lowrisc_fpga_cw340": ["--uarts=/dev/ttyACM_CW340_1,/dev/ttyACM_CW340_0"],
        "//conditions:default": [],
    }),
    base = ":fpga_cw340",
    bitstream = "//hw/bitstream/cw340:test_rom",
    exec_env = "fpga_cw340_test_rom",
    param = {
        "interface": "cw340",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    test_cmd = """
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
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
    rom_scramble_config = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
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
    rom = "//sw/device/lib/testing/test_rom:test_rom",
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
    extract_sw_logs = "//util/device_sw_utils:extract_sw_logs_db",
    flash_scramble_tool = "//util/design:gen-flash-img",
    lib = "//sw/device/lib/arch:sim_dv",
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/ip/otp_ctrl/data:img_rma",
    otp_data_perm = "//hw/ip/otp_ctrl/data:data_perm",
    otp_mmap = "//hw/ip/otp_ctrl/data:otp_ctrl_mmap.hjson",
    otp_seed = "//hw/ip/otp_ctrl/data:otp_seed",
    rom_scramble_config = "//hw/top_earlgrey/data:autogen/top_earlgrey.gen.hjson",
)

sim_dv(
    name = "sim_dv",
    testonly = True,
    base = ":sim_dv_base",
    exec_env = "sim_dv",
    rom = "//sw/device/lib/testing/test_rom:test_rom",
)
