# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "qemu_params",
)
load("@rules_cc//cc:defs.bzl", "cc_library")
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:utils.bzl",
    "create_imm_section_targets",
    "exportability_test",
)
load(
    "//sw/device/silicon_creator/rom_ext/imm_section:defs.bzl",
    "DEFAULT_EXEC_ENV",
)

package(default_visibility = ["//visibility:public"])

EXPORTS = [
    "test_string",
    "test_add",
    "memcpy",
]

PLACEMENTS = {
    "a": "{rom_ext_slot_a}",
    "b": "{rom_ext_slot_b}",
    "virtual": "{rom_ext_slot_a}",
}

VARIANTS = [
    {
        "name": "test_imm_lib",
        "copts": [],
        "expect_fail": False,
    },
    {
        "name": "test_imm_lib_bss",
        "copts": ["-DUSE_BSS"],
        "expect_fail": True,
    },
    {
        "name": "test_imm_lib_data",
        "copts": ["-DUSE_DATA"],
        "expect_fail": True,
    },
]

[
    cc_library(
        name = var["name"],
        testonly = True,
        srcs = ["test_imm_blob.c"],
        copts = var["copts"],
        deps = [
            "//sw/device/lib/base:memory",
            "//sw/device/silicon_creator/lib/base:static_critical",
            "//sw/device/silicon_creator/lib/base:static_dice",
            "//sw/device/silicon_creator/rom_ext/imm_section:imm_section_version_def",
        ],
    )
    for var in VARIANTS
]

[
    # Test imm_section binary for slot.
    opentitan_binary(
        name = "test_imm_section_bin_slot_{}".format(slot),
        testonly = True,
        exec_env = DEFAULT_EXEC_ENV,
        extra_bazel_features = [
            "minsize",
            "use_lld",
        ],
        linker_script = "//sw/device/silicon_creator/rom_ext/imm_section:ld_slot_{}".format(slot),
        manifest = "//hw/top_earlgrey:none_manifest",
        deps = [
            ":test_imm_lib",
        ],
    )
    for slot in PLACEMENTS.keys()
]

[
    # Create custom imm_section target from the test binary for slot.
    create_imm_section_targets(
        name = "test_imm_section_slot_{}".format(slot),
        testonly = True,
        src = ":test_imm_section_bin_slot_{}".format(slot),
        prefix_exports = "imm_shared_",
        exports = EXPORTS,
    )
    for slot in PLACEMENTS.keys()
]

[
    # Run the test at the rom_ext stage. The test program itself acts as the rom_ext
    # and embeds our test_imm_section in the .rom_ext_immutable section.
    opentitan_test(
        name = "export_test_slot_{}".format(slot),
        srcs = ["export_test.c"],
        exec_env = {
            "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": None,
            "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": None,
        },
        fpga = fpga_params(
            assemble = "{{firmware}}@{}".format(PLACEMENTS[slot]),
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_creator_slot_{}".format(slot),
        qemu = qemu_params(
            assemble = "{{firmware}}@{}".format(PLACEMENTS[slot]),
        ),
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
            ":test_imm_section_slot_{}".format(slot),
        ],
    )
    for slot in PLACEMENTS.keys()
]

[
    exportability_test(
        name = var["name"] + "_exportability_test",
        expect_fail = var["expect_fail"],
        exports = EXPORTS,
        deps = [":" + var["name"]],
    )
    for var in VARIANTS
]
