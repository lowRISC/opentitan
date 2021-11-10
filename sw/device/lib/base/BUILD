# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
    deps = [
        ":bitfield",
        ":csr",
        ":hardened",
        ":macros",
        ":memory",
        ":mmio_hdrs",
        ":multibits",
    ],
)

cc_library(
    name = "multibits",
    hdrs = [
        "multibits.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "macros",
    hdrs = [
        "macros.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "csr",
    hdrs = [
        "csr.h",
        "csr_registers.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "memory",
    srcs = [
        "memory.c",
    ],
    hdrs = [
        "memory.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "stdasm",
    hdrs = [
        "stdasm.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "hardened",
    srcs = [
        "hardened.c",
    ],
    hdrs = [
        "hardened.h",
    ],
    copts = [
        "-fno-builtin",
    ],
    deps = [
        ":stdasm",
    ],
)

cc_library(
    name = "bitfield",
    srcs = [
        "bitfield.c",
    ],
    hdrs = [
        "bitfield.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "mmio_hdrs",
    hdrs = [
        "mmio.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "mmio",
    srcs = [
        ":mmio_src",
    ],
    hdrs = [
        "mmio.h",
    ],
    deps = [
        ":bitfield",
        ":memory",
    ],
)

# tests need to build src with a different set of flags. use this to do so.
filegroup(
    name = "mmio_src",
    srcs = ["mmio.c"],
)
