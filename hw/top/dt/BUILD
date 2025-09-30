# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

py_library(
    name = "clkmgr_ipconfig",
    srcs = ["clkmgr_ipconfig.py"],
    deps = [
        "//util/ipgen",
    ],
)

py_library(
    name = "clkmgr_binding",
    srcs = ["clkmgr_binding.py"],
    deps = [
        ":clkmgr_ipconfig",
        "//util/dtgen:helper",
        "//util/topgen",
    ],
)

py_library(
    name = "rstmgr_ipconfig",
    srcs = ["rstmgr_ipconfig.py"],
    deps = [
        "//util/ipgen",
    ],
)

py_library(
    name = "rstmgr_binding",
    srcs = ["rstmgr_binding.py"],
    deps = [
        ":rstmgr_ipconfig",
        "//util/dtgen:helper",
        "//util/topgen",
    ],
)

py_library(
    name = "pwrmgr_ipconfig",
    srcs = ["rstmgr_ipconfig.py"],
    deps = [
        "//util/ipgen",
    ],
)

py_library(
    name = "pwrmgr_binding",
    srcs = ["pwrmgr_binding.py"],
    deps = [
        ":pwrmgr_ipconfig",
        "//util/dtgen:helper",
        "//util/topgen",
    ],
)