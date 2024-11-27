# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Cryptotest test case definition"""

load(
    "//rules/opentitan:defs.bzl",
    "fpga_params",
    "opentitan_test",
    "silicon_params",
)

# Defines default execution environments for cryptotest targets. All
# opentitan_test must have the following attributes to configure
# each execution environment:
# - cw310
# - silicon
CRYPTOTEST_EXEC_ENVS = {
    "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    "//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
    "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon",
}

FIRMWARE_DEPS = [
    "//sw/device/tests/crypto/cryptotest/firmware:aes",
    "//sw/device/tests/crypto/cryptotest/firmware:drbg",
    "//sw/device/tests/crypto/cryptotest/firmware:ecdh",
    "//sw/device/tests/crypto/cryptotest/firmware:ecdsa",
    "//sw/device/tests/crypto/cryptotest/firmware:hash",
    "//sw/device/tests/crypto/cryptotest/firmware:hmac",
    "//sw/device/tests/crypto/cryptotest/firmware:kmac",
    "//sw/device/tests/crypto/cryptotest/firmware:sphincsplus",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",

    # Include all JSON commands.
    "//sw/device/tests/crypto/cryptotest/json:commands",
]

def cryptotest(name, test_vectors, test_args, test_harness, skip_in_nightly_ci = False):
    """A macro for defining a CryptoTest test case.

    Args:
        name: the name of the test.
        test_vectors: the test vectors to use.
        test_args: additional arguments to pass to the test.
        test_harness: the test harness to use.
        skip_in_nightly_ci: indicate if the test should be run in the nightly CI.
    """
    tags = ["skip_in_nightly_ci"] if skip_in_nightly_ci else []
    opentitan_test(
        name = name,
        srcs = ["//sw/device/tests/crypto/cryptotest/firmware:firmware.c"],
        fpga = fpga_params(
            timeout = "long",
            data = test_vectors,
            tags = tags,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
        exec_env = CRYPTOTEST_EXEC_ENVS,
        silicon = silicon_params(
            timeout = "eternal",
            tags = tags,
            data = test_vectors,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
        deps = FIRMWARE_DEPS,
    )
