# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
    copts = [
        "-fno-builtin",
    ],
    srcs = [
        "bitfield.c",
        "hardened.c",
        "memory.c",
    ],
    hdrs = [
        "bitfield.h",
        "csr.h",
        "csr_registers.h",
        "hardened.h",
        "macros.h",
        "memory.h",
        "mmio.h",
        "stdasm.h",
    ],
)


cc_library(
    name = "mmio",
    srcs = [
        "mmio.c",
    ],
    hdrs = [
        "mmio.h",
    ],
    deps = [
        ":base",
    ],
)

# tests need to build src with a different set of flags. use this to do so.
filegroup(
    name = "mmio_src",
    srcs = ["mmio.c"],
)
