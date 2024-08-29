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

[
    opentitan_binary(
        name = "boot_test_{}".format(name),
        testonly = True,
        srcs = [
            "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
        ],
        exec_env = [
            "//hw/top_earlgrey:fpga_hyper310_rom_ext",
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
        name = "rescue_firmware_{}".format(name),
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "",
            binaries = {
                ":boot_test_{}".format(name): "payload",
            },
            slot = position["slot"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {rom_ext}"
                # First make sure the ROM_EXT is faulting because there is no firmware
                --exec="console --non-interactive --exit-success='BFV:' --exit-failure='PASS|FAIL'"
                # Load firmware via rescue
                --exec="rescue firmware --slot={slot} {payload:signed_bin}"
                # Check for firmware execution
                --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
                no-op
            """,
        ),
    )
    for name, position in _POSITIONS.items()
]

opentitan_test(
    name = "next_slot",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {slot_a:signed_bin}@0x10000 {slot_b:signed_bin}@0x90000",
        binaries = {
            ":boot_test_slot_a": "slot_a",
            ":boot_test_slot_b": "slot_b",
        },
        test_cmd = """
            --exec="transport init"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            # Set next slot via the rescue protocol
            --exec="rescue boot-svc set-next-bl0-slot --next=SlotB"
            # Check for firmware execution in slot B
            --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
            # Reset and observe return to slot A.
            --exec="gpio apply RESET"
            --exec="gpio remove RESET"
            --exec="console --non-interactive --exit-success='bl0_slot = AA__\r\n' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
)

opentitan_test(
    name = "primary_slot",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@0 {slot_a:signed_bin}@0x10000 {slot_b:signed_bin}@0x90000",
        binaries = {
            ":boot_test_slot_a": "slot_a",
            ":boot_test_slot_b": "slot_b",
        },
        test_cmd = """
            --exec="transport init"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            # Set primary slot via the rescue protocol
            --exec="rescue boot-svc set-next-bl0-slot --primary=SlotB"
            # Check for firmware execution in slot B
            --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
            # Reset and observe continued execution in slot B
            --exec="gpio apply RESET"
            --exec="gpio remove RESET"
            --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
            # Set primary slot via the rescue protocol
            --exec="rescue boot-svc set-next-bl0-slot --primary=SlotA"
            # Check for firmware execution in slot A
            --exec="console --non-interactive --exit-success='bl0_slot = AA__\r\n' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
)
