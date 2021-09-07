# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "bitfield",
    linkstatic = True,
    srcs = [
        "bitfield.c",
        "bitfield.h",
        ],
    )

cc_library(
    name = "mem",
    linkstatic = True,
    srcs = [
        "memory.c",
        "memory.h",
        ],
    copts = [
        "-fno-builtin",
        ],
    )


cc_library(
    name = "mmio",
    linkstatic = True,
    srcs = [
        "mmio.c",
        "mmio.h",
        ],
    deps = [
        ":bitfield",
        ":mem",
        ],
    )

cc_library(
    name = "hardened",
    linkstatic = True,
    srcs = [
        "hardened.c",
        "hardened.h",
        "stdasm.h",
        ],
    )
