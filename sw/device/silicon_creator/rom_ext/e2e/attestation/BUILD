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

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

opentitan_binary(
    name = "print_certs",
    testonly = True,
    srcs = ["print_certs.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_a",
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
        "//sw/device/silicon_creator/manuf/base:perso_tlv_data",
    ],
)

opentitan_test(
    name = "print_certs_test",
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        binaries = {
            ":print_certs": "firmware",
        },
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/attestation:attestation_test",
        testopt_bootstrap = "False",
    ),
    qemu = qemu_params(
        binaries = {
            ":print_certs": "firmware",
        },
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/attestation:attestation_test",
    ),
)
