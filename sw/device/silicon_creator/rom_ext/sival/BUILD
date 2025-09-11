# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules:const.bzl", "CONST", "hex")
load("//rules:manifest.bzl", "manifest")
load("//rules:signing.bzl", "offline_presigning_artifacts", "offline_signature_attach")
load("//rules/opentitan:defs.bzl", "opentitan_binary")
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VARIATIONS",
    "ROM_EXT_VERSION",
    "SLOTS",
)

package(default_visibility = ["//visibility:public"])

manifest(d = {
    "name": "manifest_sival",
    "identifier": hex(CONST.ROM_EXT),
    "version_major": ROM_EXT_VERSION.MAJOR,
    "version_minor": ROM_EXT_VERSION.MINOR,
    "security_version": ROM_EXT_VERSION.SECURITY,
    "visibility": ["//visibility:private"],
})

ROM_EXT_FEATURES = [
    "minsize",
    "use_lld",
]

# To test that the prod-signed SiVAL ROM_EXT boots on the FPGA, you need a bitstream
# with the sival keys pre-programmed into OTP.
# You can manually create such a bitstream with:
#
# bazel build //hw/bitstream/universal:splice \
#   --//hw/bitstream/universal:env=//hw/top_earlgrey:fpga_hyper310_rom_ext \
#   --//hw/bitstream/universal:otp=//hw/top_earlgrey/data/otp/sival_skus:otp_img_prod_manuf_personalized
[
    opentitan_binary(
        name = "rom_ext_{}_fake_slot_{}".format(variation, slot),
        collect_code_coverage = 0,
        ecdsa_key = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"},
        exec_env = [
            "//hw/top_earlgrey:silicon_creator",
            "//hw/top_earlgrey:fpga_cw310",
            "//hw/top_earlgrey:fpga_cw340",
        ],
        linker_script = "//sw/device/silicon_creator/rom_ext:ld_slot_{}".format(slot),
        # In order to prevent the linker from prematurely discarding symbols, we
        # need to give the CRT library last.
        linkopts = [
            "$(location //sw/device/silicon_creator/rom_ext:rom_ext_{})".format(variation),
            "$(location //sw/device/lib/crt)",
        ],
        manifest = ":manifest_sival",
        transitive_features = ROM_EXT_FEATURES,
        # TODO(#26060): Temporarily disable SPX signing of ROM_EXT.
        #spx_key = {"//sw/device/silicon_creator/rom/keys/fake/spx:prod_key_0_spx": "prod_key_0"},
        deps = [
            # The sival_owner C library is included only in the "fake" ROM_EXT,
            # as it is typically used to test FPGA flows and the FPGA doesn't
            # retain ownership information across bitstream reloads.
            ":sival_owner",
            "//sw/device/lib/crt",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/rom_ext:rom_ext_{}".format(variation),
            "//sw/device/silicon_creator/rom_ext/imm_section:main_section_{}_slot_{}".format(variation, slot),
        ],
    )
    for variation in ROM_EXT_VARIATIONS.keys()
    for slot in SLOTS
]

[
    opentitan_binary(
        name = "rom_ext_{}_prod_slot_{}".format(variation, slot),
        collect_code_coverage = 0,
        exec_env = [
            "//hw/top_earlgrey:silicon_creator",
            "//hw/top_earlgrey:fpga_cw310",
            "//hw/top_earlgrey:fpga_cw340",
        ],
        linker_script = "//sw/device/silicon_creator/rom_ext:ld_slot_{}".format(slot),
        linkopts = [
            "$(location //sw/device/silicon_creator/rom_ext:rom_ext_{})".format(variation),
            "$(location //sw/device/lib/crt)",
        ],
        transitive_features = ROM_EXT_FEATURES,
        deps = [
            ":sival_owner",
            "//sw/device/lib/crt",
            "//sw/device/silicon_creator/lib:manifest_def",
            "//sw/device/silicon_creator/rom_ext:rom_ext_{}".format(variation),
            "//sw/device/silicon_creator/rom_ext/imm_section:main_section_{}_slot_{}".format(variation, slot),
        ],
    )
    for variation in ROM_EXT_VARIATIONS.keys()
    for slot in SLOTS
]

offline_presigning_artifacts(
    name = "presigning",
    testonly = True,
    srcs = [
        ":rom_ext_{}_prod_slot_{}".format(variation, slot)
        for variation in ROM_EXT_VARIATIONS.keys()
        for slot in SLOTS
    ],
    ecdsa_key = {
        "//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0_ecdsa_p256",
    },
    manifest = ":manifest_sival",
    tags = ["manual"],
)

pkg_tar(
    name = "digests",
    testonly = True,
    srcs = [":presigning"],
    mode = "0644",
    tags = ["manual"],
)

offline_signature_attach(
    name = "signed",
    testonly = True,
    srcs = [
        ":presigning",
    ],
    ecdsa_signatures = [
        "//sw/device/silicon_creator/rom_ext/sival/signatures:ecdsa_signatures",
    ],
    tags = ["manual"],
)

cc_library(
    name = "sival_owner",
    srcs = ["sival_owner.c"],
    deps = [
        "//sw/device/silicon_creator/lib:boot_data",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/lib/ownership",
        "//sw/device/silicon_creator/lib/ownership:datatypes",
        "//sw/device/silicon_creator/lib/ownership:owner_block",
        "//sw/device/silicon_creator/rom_ext/sival/keys:includes",
    ],
    alwayslink = True,
)
