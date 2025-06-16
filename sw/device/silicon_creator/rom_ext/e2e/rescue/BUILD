# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")
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

package(default_visibility = ["//visibility:public"])

_POSITIONS = {
    "slot_a": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
        "slot": "SlotA",
        "rom_ext_offset": "0",
    },
    "slot_b": {
        "linker_script": "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_b",
        "slot": "SlotB",
        "rom_ext_offset": "0x80000",
    },
}

_RESCUE_ROMEXT_RESULTS = {
    True: {
        # When the ROM_EXT location and rescue upload slot are the same.
        "success": DEFAULT_TEST_SUCCESS_MSG,
        "failure": DEFAULT_TEST_FAILURE_MSG,
    },
    False: {
        # When the ROM_EXT location and rescue upload slot are opposite.
        "success": "{slot} rom_ext_id = OTRE\r\n.*{slot} rom_ext_version = 99.999\r\n",
        "failure": "(PASS|FAIL|BFV).*\r\n",
    },
}

_CONFIGS = {
    "xmodem": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_a",
        # This alternate rom_ext has enter-on-fail and a timeout enabled.
        "alt_rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_xmodem_timeout",
        "params": "",
        "setup": "",
        "tags": [],
    },
    "usbdfu": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_usbdfu",
        "params": "-p usb-dfu -t strap -v 3",
        "setup": "",
        "tags": [],
    },
    "spidfu": {
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_spidfu",
        # Use spi-dfu, trigger with GPIO IOA2 high.
        "params": "-p spi-dfu -t gpio -v +Ioa2",
        "setup": "--exec=\"gpio set --mode OpenDrain Ioa2\"",
        "tags": [],
    },
}

[
    opentitan_binary(
        name = "boot_test_{}".format(name),
        testonly = True,
        srcs = [
            "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
        ],
        defines = [
            "WITH_MANIFEST=1",
        ],
        exec_env = [
            "//hw/top_earlgrey:fpga_cw310_rom_ext",
        ],
        linker_script = position["linker_script"],
        deps = [
            "//hw/top_earlgrey/sw/autogen:top_earlgrey",
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib:manifest",
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
            changes_otp = True,
            params = config["params"],
            rom_ext = config["rom_ext"],
            setup = config["setup"],
            slot = position["slot"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                {setup}
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

# This bad ROM_EXT image is an empty image that identifies as a ROM_EXT with
# version number 99.999.  Apart from the identifier word and version, it
# is all zeros.  The identifier word allows rescue to identify the first block
# of the rescue payload as a potential ROM_EXT and possibly store it in
# flash of the inactive partition.
genrule(
    name = "bad_rom_ext",
    srcs = ["bad_rom_ext.txt"],
    outs = ["bad_rom_ext.bin"],
    cmd = "xxd -r $< > $@",
)

# Test rescue driven ROM_EXT updates:
# 1. Place a ROM_EXT in slot_a or slot_b.
# 2. Use rescue to send a rom_ext+owner_firmware payload.
# 3. If rescueing into the slot where the ROM_EXT is active, the rom_ext
#    portion of the payload should be silently consumed and not updated.
#    If rescueing into the opposite slot, the rom_ext portion of the
#    payload will be programmed into the inactive rom_ext slot.
# 4. Upon booting, the test binary will print the identifier and version
#    fields of both ROM_EXT slots.
[
    opentitan_test(
        name = "rescue_rom_ext_{}_update_{}".format(rxslot, name),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{rom_ext}@{rom_ext_offset}",
            binaries = {
                ":boot_test_{}".format(name): "payload",
                ":bad_rom_ext": "bad_rom_ext",
            },
            changes_otp = True,
            exit_failure = _RESCUE_ROMEXT_RESULTS[name == rxslot]["failure"],
            exit_success = _RESCUE_ROMEXT_RESULTS[name == rxslot]["success"].format(slot = name),
            image_name = "/tmp/rescue_rom_ext_{}.img".format(name),
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_virtual",
            rom_ext_offset = _POSITIONS[rxslot]["rom_ext_offset"],
            slot = position["slot"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {firmware}"
                # First make sure the ROM_EXT is faulting because there is no firmware
                --exec="console --non-interactive --exit-success='BFV:' --exit-failure='PASS|FAIL'"
                # Construct a firmware image with the bad ROM_EXT
                --exec="image assemble --size=131072 --mirror=false --output={image_name} {bad_rom_ext}@0 {payload}@0x10000"
                # Load firmware via rescue, including the bad ROM_EXT
                --exec="rescue firmware --raw --slot={slot} {image_name}"
                # Check for firmware execution
                --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
                no-op
            """,
        ),
    )
    for name, position in _POSITIONS.items()
    for rxslot in _POSITIONS.keys()
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
            changes_otp = True,
            params = config["params"],
            rom_ext = config["rom_ext"],
            setup = config["setup"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {firmware}"
                {setup}
                --exec="no-op --info='##### Set next slot via the rescue protocol'"
                --exec="rescue {params} boot-svc set-next-bl0-slot --next=SlotB --get-response=false"
                --exec="no-op --info='##### Check for firmware execution in slot B'"
                --exec="console --non-interactive --exit-success='bl0_slot = __BB\r\n' --exit-failure='{exit_failure}'"
                --exec="no-op --info='##### Reset and observe return to slot A.'"
                --exec="gpio apply RESET"
                --exec="gpio remove RESET"
                --exec="console --non-interactive --exit-success='bl0_slot = AA__\r\n' --exit-failure='{exit_failure}'"
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
            changes_otp = True,
            params = config["params"],
            rom_ext = config["rom_ext"],
            setup = config["setup"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                --exec="bootstrap --clear-uart=true {firmware}"
                {setup}
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
        changes_otp = True,
        test_cmd = """
            --exec="transport init"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {rom_ext}"
            # First make sure the ROM_EXT is faulting because there is no firmware
            --exec="console --non-interactive --exit-success='BFV:' --exit-failure='PASS|FAIL'"
            # Load firmware via rescue
            --exec="rescue firmware --rate=115200 {payload:signed_bin}"
            # Check for firmware execution
            --exec="console --baudrate=115200 --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
)

opentitan_test(
    name = "rescue_inactivity_timeout",
    srcs = [
        "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    fpga = fpga_params(
        changes_otp = True,
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_xmodem_timeout",
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            # Trigger rescue and do nothing.  We expect the inactivity timer to
            # cause rescue to exit and then boot the firmware.
            --exec="rescue no-op"
            # Check for firmware execution
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

opentitan_test(
    name = "rescue_inactivity_timeout_preserved_reset_reason",
    srcs = [
        "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    fpga = fpga_params(
        changes_otp = True,
        # We configure OTP to preserve the reset reason.  This tests that the
        # ROM_EXT clears power-on-reset before rebooting so that the ROM wont
        # re-scramble ret-ram and destroy the 'skip_once' request.
        otp = "//sw/device/silicon_creator/rom_ext/e2e:otp_img_secret2_locked_preserve_reset_rma",
        # We use the spidfu rom_ext because we can trigger with a GPIO and we
        # want to simulate the trigger being jammed.
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_spidfu",
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            # Set the trigger with gpio command to simulate the trigger being jammed.
            --exec="gpio set --mode PushPull --value true Ioa2"
            # Check for firmware execution.  We'll enter rescue, timeout,
            # then reboot and execute firmware.
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            no-op
        """,
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

# Check that xmodem rescue is functional when the `RESQ` mode is disabled.
opentitan_test(
    name = "xmodem_restricted_commands",
    srcs = [
        "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    fpga = fpga_params(
        changes_otp = True,
        exit_failure = "ok: ",
        exit_success = "error: mode not allowed",
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_xmodem_restricted_commands",
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            --exec="bootstrap --clear-uart=true {firmware}"
            # Trigger rescue and make sure we can get the device ID.
            --exec="rescue get-device-id --reboot=false"
            # Try the `RESQ` mode and make sure we get an error message.
            --exec="console --non-interactive --send='RESQ\r' --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            # Try the `REBO` mode and make sure we reboot without crash.
            --exec="console --non-interactive --send='REBO\r' --exit-success='ROM:' --exit-failure='BFV:.*\r\n'"
            no-op
        """,
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

# Check that DFU rescue is functional when the `RESQ` mode is disabled.
# TODO: Add a test to try to perform a firmware rescue and ensure that it fails.
opentitan_test(
    name = "spidfu_restricted_commands",
    srcs = [
        "//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test",
    ],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
    },
    fpga = fpga_params(
        changes_otp = True,
        params = "-p spi-dfu -t gpio -v +Ioa2",
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_spidfu_restricted_commands",
        setup = "--exec=\"gpio set --mode OpenDrain Ioa2\"",
        test_cmd = """
            --exec="transport init"
            --exec="fpga clear-bitstream"
            --exec="fpga load-bitstream {bitstream}"
            {setup}
            --exec="bootstrap --clear-uart=true {firmware}"
            # Trigger rescue and make sure we can get the device ID.
            --exec="rescue {params} get-device-id --reboot=false"
            no-op
        """,
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
    ],
)

[
    opentitan_test(
        name = "rescue_enter_on_fail_{}".format(name),
        exec_env = {
            "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "",
            changes_otp = True,
            exit_success = "BFV:05524304\r\n",
            rom_ext = config.get(
                "alt_rom_ext",
                config["rom_ext"],
            ),
            setup = config["setup"],
            tags = config["tags"],
            test_cmd = """
                --exec="transport init"
                --exec="fpga clear-bitstream"
                --exec="fpga load-bitstream {bitstream}"
                {setup}
                # Load only the ROM_EXT so the boot will fail because of no firmware.
                --exec="bootstrap --clear-uart=true {rom_ext}"
                # Check that the final boot-fault is "kErrorRescueInactivity".
                --exec="console --non-interactive --exit-success='{exit_success}' --timeout=10s"
                no-op
            """,
        ),
    )
    for name, config in _CONFIGS.items()
]
