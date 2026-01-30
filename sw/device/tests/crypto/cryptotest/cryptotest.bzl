# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Cryptotest test case definition"""

load(
    "@lowrisc_opentitan//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "fpga_params",
    "opentitan_test",
    "silicon_params",
)

# Defines default execution environments for cryptotest targets. All
# opentitan_test must have the following attributes to configure
# each execution environment:
# - cw310
# - cw340
# - silicon
CRYPTOTEST_EXEC_ENVS = {
    "@lowrisc_opentitan//hw/top_earlgrey:fpga_cw310_test_rom": None,
    "@lowrisc_opentitan//hw/top_earlgrey:fpga_cw310_sival_rom_ext": None,
    "@lowrisc_opentitan//hw/top_earlgrey:fpga_cw340_test_rom": "fpga_cw340",
    "@lowrisc_opentitan//hw/top_earlgrey:fpga_cw340_sival_rom_ext": "fpga_cw340",
} | EARLGREY_SILICON_OWNER_ROM_EXT_ENVS

FIRMWARE_DEPS = [
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:aes",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:aes_gcm",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:drbg",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:ecdh",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:ecdsa",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:hash",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:hmac",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:kmac",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:rsa",
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:sphincsplus",
    "@lowrisc_opentitan//sw/device/lib/base:csr",
    "@lowrisc_opentitan//sw/device/lib/base:status",
    "@lowrisc_opentitan//sw/device/lib/crypto/drivers:entropy",
    "@lowrisc_opentitan//sw/device/lib/testing/test_framework:check",
    "@lowrisc_opentitan//sw/device/lib/testing/test_framework:ottf_main",
    "@lowrisc_opentitan//sw/device/lib/testing/test_framework:ujson_ottf",
    "@lowrisc_opentitan//sw/device/lib/ujson",

    # Include all JSON commands.
    "@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/json:commands",
]

def cryptotest(name, test_vectors, test_args, test_harness, slow_test = False):
    """A macro for defining a CryptoTest test case.

    Args:
        name: the name of the test.
        test_vectors: the test vectors to use.
        test_args: additional arguments to pass to the test.
        test_harness: the test harness to use.
        slow_test: indicate if the test should be run in the nightly CI.
    """
    tags = ["slow_test"] if slow_test else []
    opentitan_test(
        name = name,
        srcs = ["@lowrisc_opentitan//sw/device/tests/crypto/cryptotest/firmware:firmware.c"],
        fpga = fpga_params(
            timeout = "long",
            data = test_vectors,
            tags = tags,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
        fpga_cw340 = fpga_params(
            timeout = "long",
            tags = tags,
            data = test_vectors,
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
