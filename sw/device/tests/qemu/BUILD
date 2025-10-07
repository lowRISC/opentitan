# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_test",
    "qemu_params",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "i2c_qemu_test",
    srcs = ["i2c_qemu_test.c"],
    exec_env = {
        "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
    },
    qemu = qemu_params(
        qemu_args = [
            "-device",
            "ds1338,bus=ot-i2c0,address=0x77",
            "-device",
            "ds1338,bus=ot-i2c1,address=0x77",
            "-device",
            "ds1338,bus=ot-i2c2,address=0x77",
            "-device",
            "i2c-echo,bus=ot-i2c0,address=0x2e",
            "-device",
            "i2c-echo,bus=ot-i2c1,address=0x2e",
            "-device",
            "i2c-echo,bus=ot-i2c2,address=0x2e",
        ],
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "i2c_qemu_target_device_test",
    srcs = ["i2c_qemu_target_device_test.c"],
    exec_env = {
        "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
        "//hw/top_earlgrey:sim_qemu_sival_rom_ext": None,
    },
    qemu = qemu_params(
        test_harness = "//sw/host/tests/qemu:i2c_target",
    ),
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:rv_plic",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
