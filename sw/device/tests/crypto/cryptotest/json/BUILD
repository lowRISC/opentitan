# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "commands",
    srcs = ["commands.c"],
    hdrs = ["commands.h"],
    deps = [
        ":aes_commands",
        ":aes_sca_commands",
        ":drbg_commands",
        ":ecdh_commands",
        ":ecdsa_commands",
        ":extclk_sca_fi_commands",
        ":hash_commands",
        ":hmac_commands",
        ":ibex_fi_commands",
        ":kmac_commands",
        ":kmac_sca_commands",
        ":otbn_fi_commands",
        ":prng_sca_commands",
        ":sha3_sca_commands",
        ":trigger_sca_commands",
        "//sw/device/lib/ujson",
    ],
)

cc_library(
    name = "aes_commands",
    srcs = ["aes_commands.c"],
    hdrs = ["aes_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "drbg_commands",
    srcs = ["drbg_commands.c"],
    hdrs = ["drbg_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "ecdsa_commands",
    srcs = ["ecdsa_commands.c"],
    hdrs = ["ecdsa_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "hmac_commands",
    srcs = ["hmac_commands.c"],
    hdrs = ["hmac_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "hash_commands",
    srcs = ["hash_commands.c"],
    hdrs = ["hash_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "ecdh_commands",
    srcs = ["ecdh_commands.c"],
    hdrs = ["ecdh_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "kmac_commands",
    srcs = ["kmac_commands.c"],
    hdrs = ["kmac_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "aes_sca_commands",
    srcs = ["aes_sca_commands.c"],
    hdrs = ["aes_sca_commands.h"],
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
    name = "extclk_sca_fi_commands",
    srcs = ["extclk_sca_fi_commands.c"],
    hdrs = ["extclk_sca_fi_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "sha3_sca_commands",
    srcs = ["sha3_sca_commands.c"],
    hdrs = ["sha3_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "sphincsplus_commands",
    srcs = ["sphincsplus_commands.c"],
    hdrs = ["sphincsplus_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "trigger_sca_commands",
    srcs = ["trigger_sca_commands.c"],
    hdrs = ["trigger_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)
