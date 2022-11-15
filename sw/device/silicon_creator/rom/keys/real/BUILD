# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "real",
    srcs = [
        "sigverify_rsa_keys_real.c",
        "//sw/device/silicon_creator/rom:sigverify_keys.h",
    ],
    hdrs = [
    ],
    tags = ["manual"],
    deps = [
        "//hw/ip/otp_ctrl/data:otp_ctrl_regs",
        "//sw/device/lib/base:macros",
        "//sw/device/silicon_creator/lib/sigverify",
    ],
)
