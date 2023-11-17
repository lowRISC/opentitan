# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:opentitan_test.bzl",
    "cw310_params",
    "opentitan_functest",
)
load(
    "//rules:const.bzl",
    "CONST",
    "get_lc_items",
    "hex",
    "hex_digits",
)
load(
    "//rules:opentitan.bzl",
    "RSA_ONLY_KEY_STRUCTS",
    "opentitan_flash_binary",
    "opentitan_multislot_flash_binary",
)
load(
    "//rules:manifest.bzl",
    "manifest",
)
load(
    "//rules:otp.bzl",
    "STD_OTP_OVERLAYS",
    "otp_image",
    "otp_json",
)
load(
    "//rules:rom_e2e.bzl",
    "maybe_skip_in_ci",
)
load(
    "//rules:splice.bzl",
    "bitstream_splice",
)
load(
    "@bazel_skylib//lib:shell.bzl",
    "shell",
)
load(
    "//sw/device/silicon_creator/rom/e2e:defs.bzl",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

SEC_VERS = [
    0,
    1,
    2,
]

[manifest({
    "name": "manifest_sec_ver_{}".format(sec_ver),
    "address_translation": hex(CONST.HARDENED_FALSE),
    "identifier": hex(CONST.ROM_EXT),
    "security_version": hex(sec_ver),
}) for sec_ver in SEC_VERS]

[opentitan_flash_binary(
    name = "empty_test_slot_{}_sec_ver_{}".format(slot, sec_ver),
    testonly = True,
    srcs = ["//sw/device/silicon_creator/rom/e2e:empty_test"],
    devices = ["fpga_cw310"],
    local_defines = [
        shell.quote("EMPTY_TEST_MSG=\"slot=%p, security_version=%01d, lc_state=0x%08x\", manifest_def_get(), manifest_def_get()->security_version, lifecycle_raw_state_get()"),
    ],
    manifest = ":manifest_sec_ver_{}".format(sec_ver),
    signed = True,
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        "//sw/device/silicon_creator/lib/sigverify:spx_verify",
    ],
) for slot in SLOTS for sec_ver in SEC_VERS]

[opentitan_multislot_flash_binary(
    name = "sec_ver_{}_{}_image".format(sec_ver_a, sec_ver_b),
    testonly = True,
    srcs = {
        ":empty_test_slot_a_sec_ver_{}".format(sec_ver_a): {
            "key": RSA_ONLY_KEY_STRUCTS[2],
            "offset": SLOTS["a"],
        },
        ":empty_test_slot_b_sec_ver_{}".format(sec_ver_b): {
            "key": RSA_ONLY_KEY_STRUCTS[2],
            "offset": SLOTS["b"],
        },
    },
    devices = ["fpga_cw310"],
) for sec_ver_a in SEC_VERS for sec_ver_b in SEC_VERS]

BOOT_POLICY_NEWER_CASES = [
    {
        "a": 0,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=0, lc_state=0x{}",
    },
    {
        "a": 0,
        "b": 1,
        "exit_success": "slot=0x20080000, security_version=1, lc_state=0x{}",
    },
    {
        "a": 1,
        "b": 0,
        "exit_success": "slot=0x20000000, security_version=1, lc_state=0x{}",
    },
    {
        "a": 1,
        "b": 1,
        "exit_success": "slot=0x20000000, security_version=1, lc_state=0x{}",
    },
]

[otp_image(
    name = "otp_img_boot_policy_newer_{}".format(lc_state),
    src = "//hw/ip/otp_ctrl/data:otp_json_{}".format(lc_state),
    overlays = STD_OTP_OVERLAYS,
) for lc_state, _ in get_lc_items()]

# Splice OTP images into bitstreams
# TODO: Add hyper310 targets?
[
    bitstream_splice(
        name = "bitstream_boot_policy_newer_{}".format(lc_state),
        src = "//hw/bitstream:rom_with_fake_keys",
        data = ":otp_img_boot_policy_newer_{}".format(lc_state),
        meminfo = "//hw/bitstream:otp_mmi",
        update_usr_access = True,
    )
    for lc_state, _ in get_lc_items()
]

[
    opentitan_functest(
        name = "boot_policy_newer_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        ),
        cw310 = cw310_params(
            bitstream = ":bitstream_boot_policy_newer_{}".format(lc_state),
            exit_success = t["exit_success"].format(hex_digits(lc_state_val)),
            tags = maybe_skip_in_ci(lc_state_val),
        ),
        key_struct = "multislot",
        ot_flash_binary = ":sec_ver_{}_{}_image".format(
            t["a"],
            t["b"],
        ),
        targets = ["cw310_rom_with_fake_keys"],
    )
    for lc_state, lc_state_val in get_lc_items()
    for t in BOOT_POLICY_NEWER_CASES
]

test_suite(
    name = "boot_policy_newer",
    tags = ["manual"],
    tests = [
        "boot_policy_newer_{}_a_{}_b_{}".format(
            lc_state,
            t["a"],
            t["b"],
        )
        for lc_state, _ in get_lc_items()
        for t in BOOT_POLICY_NEWER_CASES
    ],
)
