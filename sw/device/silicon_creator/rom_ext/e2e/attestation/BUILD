# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "print_certs_test",
    srcs = ["print_certs.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
    },
    fpga = fpga_params(
        test_cmd = """
            --bootstrap={firmware}
        """,
        test_harness = "//sw/host/tests/attestation:attestation_test",
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
    ],
)
