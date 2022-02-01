# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "base",
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
        "multibits.h",
        "multibits_asm.h",
        "stdasm.h",
    ],
    copts = [
        "-fno-builtin",
    ],
)

cc_library(
    name = "abs_mmio",
    srcs = [
        "abs_mmio.c",
    ],
    hdrs = [
        "abs_mmio.h",
    ],
    deps = [
        ":base",
    ],
)

# mock_abs_mmio is currently under sw/silicon_creator/lib/base and we need this
# header to be able to build unit tests.
filegroup(
    name = "abs_mmio_h",
    srcs = ["abs_mmio.h"],
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
