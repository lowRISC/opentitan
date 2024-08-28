# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""Cryptotest test case definition"""

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
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
# - silicon_prodc
CRYPTOTEST_EXEC_ENVS = {
    "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    "//hw/top_earlgrey:fpga_cw340_test_rom": "fpga_cw340",
    "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon",
    "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_prodc",
}

def cryptotest(name, test_vectors, test_args, test_harness):
    """A macro for defining a CryptoTest test case.

    Args:
        name: the name of the test.
        test_vectors: the test vectors to use.
        test_args: additional arguments to pass to the test.
        test_harness: the test harness to use.
    """
    opentitan_test(
        name = name,
        fpga = fpga_params(
            timeout = "long",
            binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware_fpga_cw310_test_rom": "firmware"},
            data = test_vectors,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
        fpga_cw340 = fpga_params(
            timeout = "long",
            binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware_fpga_cw340_test_rom": "firmware"},
            data = test_vectors,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
        exec_env = CRYPTOTEST_EXEC_ENVS,
        silicon = silicon_params(
            timeout = "eternal",
            binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware_silicon_owner_sival_rom_ext": "firmware"},
            data = test_vectors,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
        silicon_prodc = silicon_params(
            timeout = "eternal",
            binaries = {"//sw/device/tests/crypto/cryptotest/firmware:firmware_silicon_owner_prodc_rom_ext": "firmware"},
            data = test_vectors,
            test_cmd = """
                --bootstrap={firmware}
            """ + test_args,
            test_harness = test_harness,
        ),
    )
