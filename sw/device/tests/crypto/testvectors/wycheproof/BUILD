# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@ot_python_deps//:requirements.bzl", "requirement")

py_binary(
    name = "rsa_3072_verify_parse_testvectors",
    srcs = ["rsa_3072_verify_parse_testvectors.py"],
    deps = [
        requirement("hjson"),
    ],
)
