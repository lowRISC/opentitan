# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:manifest.bzl",
    "manifest",
)
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_cw305",
    "fpga_cw310",
    "fpga_cw340",
    "silicon",
    "sim_dv",
    "sim_qemu",
    "sim_verilator",
)
load("//rules/opentitan:qemu.bzl", "qemu_cfg", "qemu_flash", "qemu_otp")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "rtl_files",
    srcs = glob(["**"]) + [
        "//hw/top_earlgrey/data:all_files",
        "//hw/top_earlgrey/dv/verilator:all_files",
        "//hw/top_earlgrey/ip:rtl_files",
        "//hw/top_earlgrey/sw:all_files",
    ],
)

# The following definition is used to define a null manifest in the signing
# configuration for execution environments (exec_env) and opentitan_test
# and opentitan_binary rules. When building the binaries, if the manifest equals
# to this null manifest, then the signing will be skipped.
CLEAR_MANIFEST = manifest(d = {
    "name": "none_manifest",
})

###########################################################################
# FPGA CW310 Environments
###########################################################################
fpga_cw310(
    name = "fpga_cw310",
    design = "earlgrey",
    exec_env = "fpga_cw310",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:fpga_cw310",
        "//hw/top_earlgrey/sw/dt:fpga_cw310",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
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
        "//ci:lowrisc_fpga_cw310": ["--uarts=/dev/ttyACM_CW310_1,/dev/ttyACM_CW310_0"],
        "//conditions:default": [],
    }),
    base = ":fpga_cw310",
    base_bitstream = "//hw/bitstream:bitstream",
    exec_env = "fpga_cw310_test_rom",
    mmi = "//hw/bitstream:cw310_mmi",
    openocd_adapter_config = "//third_party/openocd:jtag_olimex_cfg",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    param = {
        "interface": "cw310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    rom = "//sw/device/lib/testing/test_rom:test_rom",
    test_cmd = """
        --exec="transport init"
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw310(
    name = "fpga_cw310_rom_with_fake_keys",
    testonly = True,
    base = ":fpga_cw310_test_rom",
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "test_key_0"},
    exec_env = "fpga_cw310_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    rom = "//sw/device/silicon_creator/rom:mask_rom",
)

sim_qemu(
    name = "sim_qemu_base",
    design = "earlgrey",
    exec_env = "sim_qemu_base",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_qemu",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
)

sim_qemu(
    name = "sim_qemu_rom_with_fake_keys",
    testonly = True,
    base = ":sim_qemu_base",
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "test_key_0"},
    exec_env = "sim_qemu_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    rom = "//sw/device/silicon_creator/rom:mask_rom",
)

fpga_cw310(
    name = "fpga_cw310_rom_ext",
    testonly = True,
    base = ":fpga_cw310_test_rom",
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    exec_env = "fpga_cw310_rom_ext",
    libs = [
        "//sw/device/lib/arch:boot_stage_owner",
        "//sw/device/lib/arch:fpga_cw310",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    manifest = "//sw/device/silicon_owner:manifest",
    otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
    param = {
        "interface": "cw310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "assemble": "{rom_ext}@0 {firmware}@0x10000",
    },
    rom = "//sw/device/silicon_creator/rom:mask_rom",
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
)

fpga_cw310(
    name = "fpga_hyper310_rom_with_fake_keys",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ],
    base = ":fpga_cw310",
    base_bitstream = "//hw/bitstream/hyperdebug:bitstream",
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "test_key_0"},
    exec_env = "fpga_hyper310_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    mmi = "//hw/bitstream/hyperdebug:mmi",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    param = {
        "interface": "hyper310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    rom = "//sw/device/silicon_creator/rom:mask_rom",
    test_cmd = """
        --exec="transport init"
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw310(
    name = "fpga_hyper310_rom_ext",
    testonly = True,
    base = ":fpga_hyper310_rom_with_fake_keys",
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    exec_env = "fpga_hyper310_rom_ext",
    libs = [
        "//sw/device/lib/arch:boot_stage_owner",
        "//sw/device/lib/arch:fpga_cw310",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    manifest = "//sw/device/silicon_owner:manifest",
    otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
    param = {
        "interface": "hyper310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "assemble": "{rom_ext}@0 {firmware}@0x10000",
    },
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
)

# FPGA configuration used to emulate silicon targets. This rule can be used by
# targets that require executing at the `rom_ext` stage level in flash, as well
# as SRAM programs. Use the `fpga_cw310_sival_rom_ext` execution environment to
# emulate silicon targets containing a `rom_ext` stage.
# See sw/device/tests/doc/sival/devguide.md for more details.
fpga_cw310(
    name = "fpga_cw310_sival",
    testonly = True,
    base = ":fpga_hyper310_rom_with_fake_keys",

    # PROD keys are allowed to run across all life cycle stages. This prod key
    # is used to enable execution across life cycle stages with a single
    # binary.
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = "fpga_cw310_sival",
    otp = "//hw/top_earlgrey/data/otp/sival_skus:otp_img_prod_manuf_personalized",
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
    tags = ["cw310_sival"],
)

# FPGA configuration used to emulate silicon targets containing a `rom_ext`
# stage.
# See `fpga_cw310_sival` for more details.
# Also, see sw/device/tests/doc/sival/devguide.md.
fpga_cw310(
    name = "fpga_cw310_sival_rom_ext",
    testonly = True,
    base = ":fpga_hyper310_rom_ext",
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    exec_env = "fpga_cw310_sival_rom_ext",
    libs = [
        "//sw/device/lib/arch:boot_stage_owner",
        "//sw/device/lib/arch:fpga_cw310",
    ],
    otp = "//hw/top_earlgrey/data/otp/sival_skus:otp_img_prod_manuf_personalized",
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
    tags = ["cw310_sival_rom_ext"],
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
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:fpga_cw305",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
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
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ] + select({
        "//ci:lowrisc_fpga_cw340": ["--uarts=/dev/ttyACM_CW340_1,/dev/ttyACM_CW340_0"],
        "//conditions:default": [],
    }),
    design = "earlgrey",
    exec_env = "fpga_cw340",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:fpga_cw340",
        "//hw/top_earlgrey/sw/dt:fpga_cw340",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    param = {
        "interface": "hyper340",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    test_cmd = "testing-not-supported",
)

fpga_cw340(
    name = "fpga_cw340_test_rom",
    testonly = True,
    base = ":fpga_cw340",
    base_bitstream = "//hw/bitstream/cw340:bitstream",
    exec_env = "fpga_cw340_test_rom",
    mmi = "//hw/bitstream/cw340:mmi",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    rom = "//sw/device/lib/testing/test_rom:test_rom",
    test_cmd = """
        --exec="transport init"
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw340(
    name = "fpga_cw340_rom_with_fake_keys",
    testonly = True,
    base = ":fpga_cw340",
    base_bitstream = "//hw/bitstream/cw340:bitstream",
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "test_key_0"},
    exec_env = "fpga_cw340_rom_with_fake_keys",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    mmi = "//hw/bitstream/cw340:mmi",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    rom = "//sw/device/silicon_creator/rom:mask_rom",
    test_cmd = """
        --exec="transport init"
        --exec="fpga load-bitstream {bitstream}"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

fpga_cw340(
    name = "fpga_cw340_rom_ext",
    testonly = True,
    base = ":fpga_cw340_rom_with_fake_keys",
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    exec_env = "fpga_cw340_rom_ext",
    libs = [
        "//sw/device/lib/arch:boot_stage_owner",
        "//sw/device/lib/arch:fpga_cw340",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    manifest = "//sw/device/silicon_owner:manifest",
    otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_rma",
    param = {
        "interface": "hyper340",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "assemble": "{rom_ext}@0 {firmware}@0x10000",
    },
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
)

# FPGA configuration used to emulate silicon targets. This rule can be used by
# targets that require executing at the `rom_ext` stage level in flash, as well
# as SRAM programs. Use the `fpga_cw340_sival_rom_ext` execution environment to
# emulate silicon targets containing a `rom_ext` stage.
# See sw/device/tests/doc/sival/devguide.md for more details.
fpga_cw340(
    name = "fpga_cw340_sival",
    testonly = True,
    base = ":fpga_cw340_rom_with_fake_keys",

    # PROD keys are allowed to run across all life cycle stages. This prod key
    # is used to enable execution across life cycle stages with a single
    # binary.
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    exec_env = "fpga_cw340_sival",
    otp = "//hw/top_earlgrey/data/otp/sival_skus:otp_img_prod_manuf_personalized",
    spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
    tags = ["cw340_sival"],
)

# FPGA configuration used to emulate silicon targets containing a `rom_ext`
# stage.
# See `fpga_cw340_sival` for more details.
# Also, see sw/device/tests/doc/sival/devguide.md.
fpga_cw340(
    name = "fpga_cw340_sival_rom_ext",
    testonly = True,
    base = ":fpga_cw340_rom_ext",
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    exec_env = "fpga_cw340_sival_rom_ext",
    libs = [
        "//sw/device/lib/arch:boot_stage_owner",
        "//sw/device/lib/arch:fpga_cw340",
    ],
    otp = "//hw/top_earlgrey/data/otp/sival_skus:otp_img_prod_manuf_personalized",
    rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_slot_a",
    tags = ["cw340_sival_rom_ext"],
)

###########################################################################
# Silicon Environments
###########################################################################
# This exec_env targets running software at the ROM_EXT stage on silicon.
silicon(
    name = "silicon_creator",
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ],
    design = "earlgrey",
    # TODO: Add switch to enable privdate key.
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:test_key_0_ecdsa_p256": "test_key_0"},
    exec_env = "silicon_creator",
    extract_sw_logs = "//util/device_sw_utils:extract_sw_logs_db",
    flash_scramble_tool = "//util/design:gen-flash-img",
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:silicon",
        "//hw/top_earlgrey/sw/dt:silicon",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    param = {
        "interface": "teacup",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
    },
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
    test_cmd = """
        --exec="transport init"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

silicon(
    name = "silicon_owner_sival_rom_ext",
    testonly = True,
    args = [
        "--rcfile=",
        "--logging=info",
        "--interface={interface}",
    ],
    design = "earlgrey",
    # TODO(moidx): Switch to real keys once these have been generated.
    ecdsa_key = {"//sw/device/silicon_creator/lib/ownership/keys/fake:app_prod_ecdsa": "prod_key_0"},
    exec_env = "silicon_owner_sival_rom_ext",
    extract_sw_logs = "//util/device_sw_utils:extract_sw_logs_db",
    flash_scramble_tool = "//util/design:gen-flash-img",
    libs = [
        "//sw/device/lib/arch:boot_stage_owner",
        "//sw/device/lib/arch:silicon",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    manifest = "//sw/device/silicon_owner:manifest",
    param = {
        "interface": "teacup",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "assemble": "{rom_ext}@0 {firmware}@0x10000",
    },
    # The //conditions:default ROM_EXT needs to be updated to use the following
    # target once available:
    # //sw/device/silicon_creator/rom_ext/sival/binaries:rom_ext_real_prod_signed_slot_a
    rom_ext = select({
        "//signing:test_keys": "//sw/device/silicon_creator/rom_ext/sival:rom_ext_fake_prod_signed_slot_a",
        "//conditions:default": "//sw/device/silicon_creator/rom_ext/sival:rom_ext_fake_prod_signed_slot_a",
    }),
    test_cmd = """
        --exec="transport init"
        --exec="bootstrap --clear-uart=true {firmware}"
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
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
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_verilator",
        "//hw/top_earlgrey/sw/dt:sim_verilator",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
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
        --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
        no-op
    """,
)

sim_verilator(
    name = "sim_verilator_rom_with_fake_keys",
    testonly = True,
    base = ":sim_verilator",
    ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
    manifest = "//sw/device/silicon_creator/rom_ext:manifest",
    rom = "//sw/device/silicon_creator/rom:mask_rom_sim_verilator",
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
    libs = [
        "//sw/device/lib/arch:boot_stage_rom_ext",
        "//sw/device/lib/arch:sim_dv",
        "//hw/top_earlgrey/sw/dt:sim_verilator",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_a",
    otp = "//hw/top_earlgrey/data/otp:img_rma",
    otp_data_perm = "//util/design/data:data_perm",
    otp_mmap = "//hw/top_earlgrey/data/otp:otp_ctrl_mmap.hjson",
    otp_seed = "//util/design/data:otp_seed",
    rom_scramble_config = "//hw/top_earlgrey/data/autogen:top_earlgrey.gen.hjson",
)

sim_dv(
    name = "sim_dv",
    testonly = True,
    base = ":sim_dv_base",
    exec_env = "sim_dv",
    rom = "//sw/device/lib/testing/test_rom:test_rom",
)
