# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
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
load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")

package(default_visibility = ["//visibility:public"])

_POSITIONS = {
    "slot_a": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "slot": "SlotA",
    },
    "slot_b": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "slot": "SlotB",
    },
}

_CONFIGS = {
    "xmodem": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        "params": "",
        "tags": [],
    },
    "usbdfu": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_usbdfu",
        "params": "-p usb-dfu -t strap -v 3",
        "tags": ["broken"],
    },
}

[
    opentitan_binary(
        name = "boot_test_{}".format(name),
        testonly = True,
        srcs = [
            "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
        ],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_ext",
        ],
        linker_script = position["linker_script"],
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
        ],
    )
    for name, position in _POSITIONS.items()
]

[
    opentitan_test(
        name = "rescue_firmware_{}_{}".format(name, protocol),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "",
            binaries = {
                ":boot_test_{}".format(name): "payload",
            },
            params = config["params"],
            rom_ext = config["rom_ext"],
            slot = position["slot"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {rom_ext}"
                # First make sure the ROM_EXT is faulting because there is no firmware
                --exec="console --non-interactive --exit-success='BFV:' --exit-failure='PASS|FAIL'"
                # Load firmware via rescue
                --exec="rescue {params} firmware --slot={slot} {payload:signed_bin}"
                # Check for firmware execution
                --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
                no-op
            """,
        ),
    )
    for name, position in _POSITIONS.items()
    for protocol, config in _CONFIGS.items()
]

[
    opentitan_test(
        name = "next_slot_{}".format(protocol),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{rom_ext}@{rom_ext_slot_a} {slot_a:signed_bin}@{owner_slot_a} {slot_b:signed_bin}@{owner_slot_b}",
            binaries = {
                ":boot_test_slot_a": "slot_a",
                ":boot_test_slot_b": "slot_b",
            },
            params = config["params"],
            rom_ext = config["rom_ext"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {firmware}"
                --exec="no-op --info='##### Set next slot via the rescue protocol'"
                --exec="rescue {params} boot-svc set-next-bl0-slot --next=SlotB --get-response=false"
                --exec="no-op --info='##### Check for firmware execution in slot B'"
                --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
                --exec="no-op --info='##### Reset and observe return to slot A.'"
                --exec="gpio apply RESET"
                --exec="gpio remove RESET"
                --exec="console --non-interactive --exit-success='bl0_slot = AA__\r\n' --exit-failure='{exit_failure}'"
                --exec="fpga clear-bitstream"
                no-op
            """,
        ),
    )
    for protocol, config in _CONFIGS.items()
]

[
    opentitan_test(
        name = "primary_slot_{}".format(protocol),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{rom_ext}@{rom_ext_slot_a} {slot_a:signed_bin}@{owner_slot_a} {slot_b:signed_bin}@{owner_slot_b}",
            binaries = {
                ":boot_test_slot_a": "slot_a",
                ":boot_test_slot_b": "slot_b",
            },
            params = config["params"],
            rom_ext = config["rom_ext"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {firmware}"
                --exec="no-op --info='##### Set primary slot via the rescue protocol'"
                --exec="rescue {params} boot-svc set-next-bl0-slot --primary=SlotB"
                --exec="no-op --info='##### Check for firmware execution in slot B'"
                --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
                --exec="no-op --info='##### Reset and observe continued execution in slot B'"
                --exec="gpio apply RESET"
                --exec="gpio remove RESET"
                --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
                --exec="no-op --info='##### Set primary slot via the rescue protocol'"
                --exec="rescue {params} boot-svc set-next-bl0-slot --primary=SlotA --get-response=false"
                --exec="no-op --info='##### Check for firmware execution in slot A'"
                --exec="console --non-interactive --exit-success='bl0_slot = AA__\r\n' --exit-failure='{exit_failure}'"
                --exec="fpga clear-bitstream"
                no-op
            """,
        ),
    )
    for protocol, config in _CONFIGS.items()
]

opentitan_test(
    name = "rescue_rate_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "",
        binaries = {
            ":boot_test_slot_a": "payload",
        },
        test_cmd = """
            --exec="transport init"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {rom_ext}"
            # First make sure the ROM_EXT is faulting because there is no firmware
            --exec="console --non-interactive --exit-success='BFV:' --exit-failure='PASS|FAIL'"
            # Load firmware via rescue
            --exec="rescue firmware --rate=230400 {payload:signed_bin}"
            # Check for firmware execution
            --exec="console --baudrate=115200 --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
)
