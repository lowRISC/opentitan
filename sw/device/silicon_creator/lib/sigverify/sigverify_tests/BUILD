# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "autogen_cryptotest_header")
load("@ot_python_deps//:requirements.bzl", "requirement")
load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

_TEST_VECTORS = [
    "//sw/host/cryptotest/testvectors/data:wycheproof_ecdsa_p256_sha256.json",
]

_TEST_ARGS = " ".join([
    "--ecdsa-json=\"$(rootpath {})\"".format(target)
    for target in _TEST_VECTORS
])

opentitan_test(
    name = "sigverify_cryptotest",
    srcs = ["sigverify_cryptotest.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_cw340_test_rom": None,
    },
    fpga = fpga_params(
        timeout = "moderate",
        data = _TEST_VECTORS,
        test_cmd = """
                --bootstrap={firmware}
            """ + _TEST_ARGS,
        test_harness = "//sw/host/tests/crypto/ecdsa_kat:harness",
    ),
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/silicon_creator/lib:otbn_boot_services",
        "//sw/device/silicon_creator/lib/drivers:hmac",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_key",
        "//sw/device/silicon_creator/lib/sigverify:ecdsa_p256_verify",
        "//sw/device/tests/crypto/cryptotest/json:commands",
        "//sw/device/tests/crypto/cryptotest/json:ecdsa_commands",
    ],
)

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
