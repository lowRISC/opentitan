# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "shake",
    srcs = ["shake.c"],
    hdrs = ["shake.h"],
    include_prefix = "third_party/embedpqc",
    strip_include_prefix = ".",
    deps = [
        "//sw/device/lib/base:hardened",
        "//sw/device/silicon_creator/lib/drivers:kmac",
    ],
)

cc_library(
    name = "mldsa44_tiny_caller",
    srcs = [
        "mldsa44_tiny_caller.S",
        "mldsa_caller_common.h",
    ],
    hdrs = ["mldsa44_tiny_caller.h"],
    deps = [
        "//third_party/embedpqc:mldsa44_tiny",
    ],
)
