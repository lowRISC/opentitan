# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "mpsse",
    srcs = [
        "mpsse/mpsse.c",
        "mpsse/support.c",
        "mpsse/support.h",
    ],
    hdrs = [
        "mpsse/mpsse.h",
    ],
    copts = [
        # TODO: Remove this once https://github.com/lowRISC/opentitan/issues/3182
        # is resolved.
        "-Wno-error=deprecated-declarations",
    ],
    linkopts = [
        "-lftdi1",
        "-lusb-1.0",
    ],
)
