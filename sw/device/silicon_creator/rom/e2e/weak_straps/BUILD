# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "CLEAR_TEST_CMD",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)
load(":gpio.bzl", "strap_combinations_test")

package(default_visibility = ["//visibility:public"])

opentitan_binary(
    name = "straps_unsigned",
    testonly = True,
    srcs = ["sw_straps_test.c"],
    exec_env = [
        "//hw/top_earlgrey:sim_verilator",
    ],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
    ],
)

strap_combinations_test(
    name = "e2e_weak_straps",
    env_firmware = {
        # When running against the test_rom, we want to run a binary that
        # prints the detected strap value.
        #
        # Furthermore, we can leave the test_rom variant of this test disabled
        # because the `sw_strap_value` test below effectively tests the same
        # thing: whether the chip can read the weak/strong values.
        #"//hw/top_earlgrey:sim_verilator": ":straps_unsigned",

        # When running against the mask_rom, we don't want a binary loaded
        # so that sigverify will be skipped and the ROM will fault quickly.
        # We'll detect whether or not the two strap combinations known to
        # the ROM affect its execution correctly.  In all other cases,
        # observing a fault is the correct outcome.
        #
        # We want the mask_rom variant enabled because it tests that the
        # ROM recognizes its two strapping values and no others.
        "//hw/top_earlgrey:sim_verilator_rom_with_fake_keys": "empty.vmem",
    },
    tags = [
        "verilator",
    ],
)

opentitan_test(
    name = "sw_strap_value",
    srcs = ["sw_straps_test.c"],
    exec_env = {
        "//hw/top_earlgrey:sim_verilator": None,
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": None,
    },
    silicon = silicon_params(
        test_cmd = """
            --bootstrap="{firmware}"
        """,
        test_harness = "//sw/host/tests/rom/sw_strap_value",
    ),
    verilator = verilator_params(
        timeout = "long",
        # This test can take > 40 minutes, so mark it manual as it shouldn't
        # run in CI/nightlies.
        tags = ["manual"],
        test_cmd = CLEAR_TEST_CMD,
        test_harness = "//sw/host/tests/rom/sw_strap_value",
    ),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:gpio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/testing:pinmux_testutils",
        "//sw/device/lib/testing/json:command",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
    ],
)
