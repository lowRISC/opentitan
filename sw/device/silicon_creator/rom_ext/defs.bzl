# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def secver_write_selection():
    """Return the secver_write value based on the configuration setting."""
    return select({
        "//sw/device/silicon_creator/rom_ext:secver_write_true": "true",
        "//conditions:default": "false",
    })

# The ROM_EXT version number to encode into the manifest.
# NOTE: the version numbers are integers, but have to be encoded as strings
# because of how the bazel rule accepts attributes.
ROM_EXT_VERSION = struct(
    MAJOR = "0",
    MINOR = "110",
    SECURITY = "0",
)

ROM_EXT_VARIATIONS = {
    "dice_x509": [
        "//sw/device/silicon_creator/lib/cert:dice",
    ],
    "dice_cwt": [
        "//sw/device/silicon_creator/lib/cert:dice_cwt",
    ],
}

SLOTS = [
    "a",
    "b",
    "virtual",
]

TEST_OWNER_CONFIGS = {
    "hybrid_owner_keys": {
        # Enable hybrid ECDSA/SPX+ ownership.
        "owner_defines": ["TEST_OWNER_KEY_ALG_HYBRID_SPX_PURE=1"],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
    "hybrid_owner_update_newversion": {
        # Enable hybrid ECDSA/SPX+ ownership.
        "owner_defines": [
            "TEST_OWNER_UPDATE_MODE=kOwnershipUpdateModeNewVersion",
            "TEST_OWNER_KEY_ALG_HYBRID_SPX_PREHASH=1",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
    "owner_update_newversion": {
        # Enable the NewVersion update mode of ownership.
        "owner_defines": ["TEST_OWNER_UPDATE_MODE=kOwnershipUpdateModeNewVersion"],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
    "usbdfu": {
        # Enable USB-DFU triggered by SW_STRAPS value 3.
        "owner_defines": [
            # 0x55 is 'U'sb.
            "WITH_RESCUE_PROTOCOL=0x55",
            # Trigger 2 is strap pins combination.
            "WITH_RESCUE_TRIGGER=2",
            # Strapping value of 3.
            "WITH_RESCUE_INDEX=3",
            # Timeout: 0x80=enter_on_fail, 0x05 = 5 seconds.
            "WITH_RESCUE_TIMEOUT=0x85",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_usbdfu"],
    },
    "spidfu": {
        "owner_defines": [
            # 0x53 is 'S'pi.
            "WITH_RESCUE_PROTOCOL=0x53",
            # Trigger 3 is GPIO pin.
            "WITH_RESCUE_TRIGGER=3",
            # When the trigger is GPIO, the index is the MuxedPad to us as the sense
            # input. Index 2 is kTopEarlgreyMuxedPadsIoa2.
            "WITH_RESCUE_INDEX=2",
            # GPIO param 3 means enable the internal pull resistor and trigger
            # rescue when the GPIO is high.
            "WITH_RESCUE_GPIO_PARAM=3",
            # Timeout: 0x80=enter_on_fail, 0x05 = 5 seconds.
            "WITH_RESCUE_TIMEOUT=0x85",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_spidfu"],
    },
    "xmodem_timeout": {
        # Enable Xmodem rescue with enter-on-fail and a timeout.
        "owner_defines": [
            # 0x58 is 'X'modem.
            "WITH_RESCUE_PROTOCOL=0x58",
            # Timeout: 0x80=enter_on_fail, 0x05 = 5 seconds.
            "WITH_RESCUE_TIMEOUT=0x85",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
    "xmodem_restricted_commands": {
        # Enable Xmodem rescue with enter-on-fail and a timeout.
        "owner_defines": [
            # 0x58 is 'X'modem.
            "WITH_RESCUE_PROTOCOL=0x58",
            # Restrict rescue to only one command
            "WITH_RESCUE_COMMAND_ALLOW=kRescueModeOpenTitanID",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
    "spidfu_restricted_commands": {
        # Enable USB-DFU triggered by SW_STRAPS value 3.
        "owner_defines": [
            # 0x53 is 'S'pi.
            "WITH_RESCUE_PROTOCOL=0x53",
            # Trigger 3 is GPIO pin.
            "WITH_RESCUE_TRIGGER=3",
            # When the trigger is GPIO, the index is the MuxedPad to us as the sense
            # input. Index 2 is kTopEarlgreyMuxedPadsIoa2.
            "WITH_RESCUE_INDEX=2",
            # GPIO param 3 means enable the internal pull resistor and trigger
            # rescue when the GPIO is high.
            "WITH_RESCUE_GPIO_PARAM=3",
            # Timeout: 0x80=enter_on_fail, 0x00 = No timeout.
            "WITH_RESCUE_TIMEOUT=0x80",
            # Restrict rescue to only one command
            "WITH_RESCUE_COMMAND_ALLOW=kRescueModeOpenTitanID",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_spidfu"],
    },
    "xmodem_rescue_disability": {
        # Enable Xmodem rescue with enter-on-fail and a timeout.
        "owner_defines": [
            # 0x58 is 'X'modem.
            "WITH_RESCUE_PROTOCOL=0x58",
            # Disallow all the rescue commands.
            "WITH_RESCUE_COMMAND_ALLOW",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
    "spidfu_rescue_disability": {
        "owner_defines": [
            # 0x53 is 'S'pi.
            "WITH_RESCUE_PROTOCOL=0x53",
            # Trigger 3 is GPIO pin.
            "WITH_RESCUE_TRIGGER=3",
            # When the trigger is GPIO, the index is the MuxedPad to us as the sense
            # input. Index 2 is kTopEarlgreyMuxedPadsIoa2.
            "WITH_RESCUE_INDEX=2",
            # GPIO param 3 means enable the internal pull resistor and trigger
            # rescue when the GPIO is high.
            "WITH_RESCUE_GPIO_PARAM=3",
            # Timeout: 0x80=enter_on_fail, 0x05 = 5 seconds.
            "WITH_RESCUE_TIMEOUT=0x85",
            # Disallow all the rescue commands.
            "WITH_RESCUE_COMMAND_ALLOW",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_spidfu"],
    },
    "isfb": {
        "owner_defines": [
            "WITH_ISFB=1",
        ],
        "rescue_module": ["//sw/device/silicon_creator/lib/rescue:rescue_xmodem"],
    },
}
