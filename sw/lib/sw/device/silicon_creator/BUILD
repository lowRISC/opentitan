# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan.bzl", "OPENTITAN_CPU")
load("//rules:opentitan_test.bzl", "opentitan_functest")
load("//rules:cross_platform.bzl", "dual_cc_library", "dual_inputs")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "cfi",
    hdrs = [
        "cfi.h",
    ],
    deps = [
        "//sw/lib/sw/device/base:hardened",
    ],
)

cc_library(
    name = "epmp_defs",
    hdrs = [
        "epmp_defs.h",
    ],
)

cc_library(
    name = "epmp_state",
    srcs = ["epmp_state.c"],
    hdrs = [
        "epmp_state.h",
    ],
    deps = [
        ":epmp_defs",
        ":error",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:hardened",
    ],
)

cc_library(
    name = "epmp_test_unlock",
    srcs = ["epmp_test_unlock.c"],
    hdrs = ["epmp_test_unlock.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":epmp_state",
        "//sw/lib/sw/device/arch:device",
        "//sw/lib/sw/device/base:csr",
    ],
)

cc_library(
    name = "error",
    hdrs = ["error.h"],
    deps = [
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:hardened",
        "//sw/lib/sw/device/base/internal:status",
    ],
)

cc_library(
    name = "keymgr_binding",
    hdrs = ["keymgr_binding_value.h"],
)

cc_library(
    name = "manifest",
    hdrs = [
        "manifest.h",
    ],
    deps = [
        ":epmp_state",
        ":error",
        ":keymgr_binding",
        "//sw/device/silicon_creator/lib/drivers:lifecycle",
        "//sw/lib/sw/device/silicon_creator/base:chip",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
        "//sw/lib/sw/device/silicon_creator/sigverify:spx_key",
    ],
)

cc_library(
    name = "dbg_print",
    srcs = ["dbg_print.c"],
    hdrs = ["dbg_print.h"],
    deps = [
        ":epmp_defs",
        ":error",
        "//sw/device/silicon_creator/lib/drivers:uart",
        "//sw/lib/sw/device/base:bitfield",
        "//sw/lib/sw/device/base:csr",
        "//sw/lib/sw/device/base:macros",
    ],
)

cc_library(
    name = "rom_patch",
    srcs = ["rom_patch.c"],
    hdrs = ["rom_patch.h"],
    deps = [
        ":error",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/silicon_creator/lib/drivers:ibex",
        "//sw/device/silicon_creator/lib/drivers:otp",
        "//sw/lib/sw/device/base:hardened_memory",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/base:multibits",
        "//sw/lib/sw/device/silicon_creator:dbg_print",
        "//sw/lib/sw/device/silicon_creator/sigverify",
    ],
)

dual_cc_library(
    name = "crc32",
    srcs = dual_inputs(
        device = ["crc32.c"],
        host = ["mock_crc32.cc"],
    ),
    hdrs = dual_inputs(
        host = ["mock_crc32.h"],
        shared = ["crc32.h"],
    ),
    # This library is a dependancy of the ujson library.
    # TODO: limit the subpackages under sw to top specific sw directories
    visibility = [
        "//sw:__subpackages__",
        "//sw/lib/sw/device/ujson:__pkg__",
    ],
    deps = dual_inputs(
        host = [
            "//sw/lib/sw/device/base:global_mock",
            "@googletest//:gtest",
        ],
        shared = [
            "//sw/lib/sw/device/base:memory",
            "//sw/lib/sw/device/base:macros",
        ],
    ),
)

cc_library(
    name = "attestation",
    hdrs = ["attestation.h"],
)

cc_library(
    name = "otbn_boot_services",
    srcs = ["otbn_boot_services.c"],
    hdrs = ["otbn_boot_services.h"],
    # This target uses OTBN pointers internally, so it cannot work host-side.
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":attestation",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/drivers:keymgr",
        "//sw/device/silicon_creator/lib/drivers:otbn",
        "//sw/lib/sw/device/base:macros",
        "//sw/lib/sw/device/silicon_creator:dbg_print",
        "//sw/lib/sw/device/silicon_creator:error",
        "//sw/lib/sw/device/silicon_creator/base:sec_mmio",
        "//sw/lib/sw/device/silicon_creator/sigverify:rsa_key",
    ],
)

opentitan_functest(
    name = "otbn_boot_services_functest",
    srcs = ["otbn_boot_services_functest.c"],
    # This target uses OTBN pointers internally, so it cannot work host-side.
    deps = [
        ":otbn_boot_services",
        "//hw/top_darjeeling/sw/autogen:top_darjeeling",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/lib/sw/device/runtime:log",
        "//sw/otbn/crypto:boot",
        "//sw/top_darjeeling/sw/device/runtime:print",
        "//sw/top_darjeeling/sw/test/utils:keymgr_testutils",
    ],
)

exports_files([
    "boot_data.h",
    "boot_data.c",
    "boot_data_functest.c",
    "chip_info.h",
    "crc32_functest.c",
    "crc32_perftest.c",
    "irq_asm_functest.c",
    "manifest.c",
    "manifest.h",
    "manifest_def.c",
    "manifest_def.h",
    "mock_boot_data.h",
    "mock_manifest.h",
    "mock_shutdown.h",
    "rom_patch.c",
    "rom_patch.h",
    "shutdown.c",
    "shutdown.h",
])

exports_files(glob(["*.cc"]))
