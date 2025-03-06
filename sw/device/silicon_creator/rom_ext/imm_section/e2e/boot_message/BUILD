# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/imm_rom_ext:defs.bzl",
    "IMMUTABLE_HASH_UNENFORCED_MSG",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "boot_test",
    srcs = ["//sw/device/silicon_creator/imm_rom_ext/e2e:empty_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        exit_success = "\nIMM_ROM_EXT:",
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "hash_unenforced_test",
    srcs = ["//sw/device/silicon_creator/imm_rom_ext/e2e:empty_test"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        exit_success = IMMUTABLE_HASH_UNENFORCED_MSG,
    ),
    deps = [
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
