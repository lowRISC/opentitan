# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(["LICENSE"])

cc_library(
    name = "ct",
    hdrs = ["ct.h"],
)

cc_library(
    name = "mldsa_mu",
    srcs = ["mldsa_mu.c"],
    hdrs = ["mldsa_mu.h"],
    deps = [
        "//third_party/embedpqc/ports:shake",
    ],
)

cc_library(
    name = "mldsa_tiny_common",
    srcs = ["mldsa_tiny_common.c"],
    hdrs = ["mldsa_tiny_common.h"],
    deps = [
        ":ct",
        "//third_party/embedpqc/ports:shake",
    ],
)

cc_library(
    name = "mldsa44_tiny",
    srcs = ["mldsa44_tiny.c"],
    hdrs = ["mldsa44_tiny.h"],
    deps = [
        ":ct",
        ":mldsa_mu",
        ":mldsa_tiny_common",
        "//third_party/embedpqc/ports:shake",
    ],
)
