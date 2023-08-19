# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_cryptotest_header")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

autogen_cryptotest_header(
    name = "sigverify_testvectors_hardcoded",
    hjson = "//sw/device/tests/crypto/testvectors:rsa_3072_verify_testvectors_hardcoded",
    template = ":sigverify_testvectors.h.tpl",
    tool = ":sigverify_set_testvectors",
)

autogen_cryptotest_header(
    name = "sigverify_testvectors_wycheproof",
    hjson = "//sw/device/tests/crypto/testvectors:rsa_3072_verify_testvectors_wycheproof",
    template = ":sigverify_testvectors.h.tpl",
    tool = ":sigverify_set_testvectors",
)

py_binary(
    name = "sigverify_set_testvectors",
    srcs = ["sigverify_set_testvectors.py"],
    imports = ["."],
    deps = [
        "//util/design/lib:common",
        requirement("hjson"),
        requirement("mako"),
        requirement("pycryptodome"),
    ],
)

filegroup(
    name = "template_files",
    srcs = [
        "sigverify_testvectors.h.tpl",
    ],
)
