# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules:certificates.bzl",
    "certificate_template",
)

package(default_visibility = ["//visibility:public"])

certificate_template(
    name = "generic_template",
    template = "//sw/host/ot_certs:generic_cert",
)

certificate_template(
    name = "example_template",
    template = "//sw/host/ot_certs:example_cert",
)

certificate_template(
    name = "uds_template",
    template = "uds.hjson",
)

certificate_template(
    name = "cdi_0_template",
    template = "cdi_0.hjson",
)

certificate_template(
    name = "cdi_1_template",
    template = "cdi_1.hjson",
)

cc_library(
    name = "asn1",
    srcs = ["asn1.c"],
    hdrs = ["asn1.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
    ],
)

cc_test(
    name = "asn1_unittest",
    srcs = ["asn1_unittest.cc"],
    deps = [
        ":asn1",
        "@googletest//:gtest_main",
    ],
)
