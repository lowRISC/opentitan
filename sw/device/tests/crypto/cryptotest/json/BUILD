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
        ":drbg_commands",
        ":ecdh_commands",
        ":ecdsa_commands",
        ":hash_commands",
        ":hmac_commands",
        ":kmac_commands",
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
    name = "sphincsplus_commands",
    srcs = ["sphincsplus_commands.c"],
    hdrs = ["sphincsplus_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)
