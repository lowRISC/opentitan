# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_binary")

package(default_visibility = ["//visibility:public"])

otbn_binary(
    name = "smoke_test",
    srcs = [
        "smoke_test.s",
    ],
    args = [
        "--defsym",
        "deterministic=1",
    ],
)

filegroup(
    name = "smoke_test_elf",
    srcs = [":smoke_test"],
    output_group = "elf",
)

sh_test(
    name = "smoke_test_sim_verilator",
    srcs = [":run_smoke.sh"],
    data = [
        ":smoke_expected.txt",
        ":smoke_test_elf",
        "//hw/ip/otbn/dv/otbnsim:stepped",
        "//hw/ip/otbn/dv/verilator:otbn_sim_verilator",
    ],
    env = {
        "VERILATOR_SIM": "$(location //hw/ip/otbn/dv/verilator:otbn_sim_verilator)",
        "SMOKE_TEST_ELF": "$(location :smoke_test_elf)",
        "SMOKE_EXPECTED": "$(location :smoke_expected.txt)",
        "OTBNSIM_STEPPED": "$(location //hw/ip/otbn/dv/otbnsim:stepped)",
    },
)
