# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "commands",
    srcs = ["commands.c"],
    hdrs = ["commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "aes_commands",
    srcs = ["aes_commands.c"],
    hdrs = ["aes_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "aes_sca_commands",
    srcs = ["aes_sca_commands.c"],
    hdrs = ["aes_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)

cc_library(
    name = "prng_sca_commands",
    srcs = ["prng_sca_commands.c"],
    hdrs = ["prng_sca_commands.h"],
    deps = ["//sw/device/lib/ujson"],
)
