# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "commands",
    srcs = ["commands.c"],
    hdrs = ["commands.h"],
    deps = [
        ":aes_sca_commands",
        ":crypto_fi_commands",
        ":extclk_sca_fi_commands",
        ":ibex_fi_commands",
        ":kmac_sca_commands",
        ":otbn_fi_commands",
        ":prng_sca_commands",
        ":rom_fi_commands",
        ":sha3_sca_commands",
        ":trigger_sca_commands",
        "//sw/device/lib/ujson",
    ],
)

cc_library(
    name = "aes_sca_commands",
    srcs = ["aes_sca_commands.c"],
    hdrs = ["aes_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "crypto_fi_commands",
    srcs = ["crypto_fi_commands.c"],
    hdrs = ["crypto_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "extclk_sca_fi_commands",
    srcs = ["extclk_sca_fi_commands.c"],
    hdrs = ["extclk_sca_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "ibex_fi_commands",
    srcs = ["ibex_fi_commands.c"],
    hdrs = ["ibex_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "ibex_sca_commands",
    srcs = ["ibex_sca_commands.c"],
    hdrs = ["ibex_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "kmac_sca_commands",
    srcs = ["kmac_sca_commands.c"],
    hdrs = ["kmac_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "otbn_fi_commands",
    srcs = ["otbn_fi_commands.c"],
    hdrs = ["otbn_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "prng_sca_commands",
    srcs = ["prng_sca_commands.c"],
    hdrs = ["prng_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "rng_fi_commands",
    srcs = ["rng_fi_commands.c"],
    hdrs = ["rng_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "rom_fi_commands",
    srcs = ["rom_fi_commands.c"],
    hdrs = ["rom_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "sca_lib_commands",
    srcs = ["sca_lib_commands.c"],
    hdrs = ["sca_lib_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "sha3_sca_commands",
    srcs = ["sha3_sca_commands.c"],
    hdrs = ["sha3_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "trigger_sca_commands",
    srcs = ["trigger_sca_commands.c"],
    hdrs = ["trigger_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)
