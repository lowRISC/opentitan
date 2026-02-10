# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:linker.bzl", "ld_library")
load("//rules:manifest.bzl", "manifest")
load("//rules/opentitan:defs.bzl", "cw310_params", "fpga_params", "opentitan_test")
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VERSION",
)

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
    "return_boot_failed": {
        "defines": ["RETURN_TO_ROM_EXT=1"],
        "exit_success": "BFV:01524509",  # kErrorRomExtBootFailed
    },
}

[
    opentitan_test(
        name = "fault_{}".format(name),
        srcs = [
            "fault_start.S",
            "fault_test.c",
        ],
        defines = test_data["defines"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        },
        fpga = fpga_params(
            exit_success = test_data["exit_success"],
        ),
        linker_script = ":ld_slot_a",
        manifest = "//sw/device/silicon_owner:manifest",
        deps = [
            "//hw/ip/uart/data:uart_c_regs",
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

opentitan_test(
    name = "epmp_test",
    srcs = ["epmp_print.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        # Note: the application stage may have a dependency on the ePMP
        # configuration.  If you are making changes to the ePMP layout,
        # you need to check that your changes won't negatively affect
        # the handoff to the application.
        exit_success = "\r\n".join([
            "0: 00000000 ----- ---- sz=00000000",
            "1: 00000000 ----- ---- sz=00000000",
            "2: a....... ----- ---- sz=00000000",  # Application code start.
            "3: a.......   TOR -X-R sz=........",  # Application code end.
            "4: a0000000 NAPOT ---R sz=00080000",  # Application rodata region.
            "5: 00000000 ----- ---- sz=00000000",
            "6: 00000000 ----- ---- sz=00000000",
            "7: 00000000 ----- ---- sz=00000000",
            "8: 2....... ----- ---- sz=00000000",  # ROM_EXT code start.
            "9: 2.......   TOR -X-R sz=........",  # ROM_EXT code end.
            "10: 00000000 ----- ---- sz=00000000",
            "11: 1001c000   NA4 ---- sz=00000004",  # Stack guard.
            "12: 20000000 NAPOT ---R sz=00100000",  # Entire flash region.
            "13: 00010000 NAPOT -XWR sz=00001000",  # RvDM regionn
            "14: 40000000 NAPOT --WR sz=10000000",  # MMIO for peripherals.
            "15: 10000000 NAPOT --WR sz=00020000",  # All of RAM.
            "mseccfg = 00000006",  # rlb=true, mmwp=true, mml=false
            ".*",
            ".*PASS!",
            "",
        ]),
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:dbg_print",
    ],
)

SRAM_EXEC_TESTCASES = [
    {
        "name": "enabled",
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_owner_sram_exec_enabled",
        "exit_success": "value = 00000006, 00000006, 00000001[\\s\\S]*PASS!",
    },
    {
        "name": "disabled",
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_owner_sram_exec_disabled",
        "exit_success": "value = 00000009, 00000006, 00000001[\\s\\S]*PASS!",
    },
    {
        "name": "disabled_locked",
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
        "exit_success": "value = 00000009, 00000009, 00000000[\\s\\S]*MCAUSE=00000001",
    },
]

[
    opentitan_test(
        name = "sram_exec_{}_test".format(test["name"]),
        srcs = ["sram_exec_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        },
        fpga = fpga_params(
            changes_otp = True,
            exit_success = test["exit_success"],
            rom_ext = test["rom_ext"],
            testopt_clear_before_test = "True",
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        deps = [
            "//hw/ip/sram_ctrl/data:sram_ctrl_c_regs",
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:abs_mmio",
            "//sw/device/lib/base:macros",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:dbg_print",
        ],
    )
    for test in SRAM_EXEC_TESTCASES
]

opentitan_test(
    name = "rom_ext_device_status_test",
    srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        device_status = "0x1",
        needs_jtag = True,
        owner_fw_version = "0",
        rom_ext_sec_version = ROM_EXT_VERSION.SECURITY,
        rom_ext_version = ROM_EXT_VERSION.MINOR,
        test_cmd = """
            --wait-for="PASS!"
            --rom-ext-version="{rom_ext_version}"
            --rom-ext-sec-version="{rom_ext_sec_version}"
            --owner-fw-version="{owner_fw_version}"
            --device-status="{device_status}"
        """,
        test_harness = "//sw/host/tests/rom_ext/device_status",
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)
