# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "cw310_params",
    "opentitan_test",
)

package(default_visibility = ["//visibility:public"])

opentitan_test(
    name = "spi_host_macronix_flash_test",
    srcs = ["spi_host_macronix_flash_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:spi_host_flash_test_impl",
    ],
)

opentitan_test(
    name = "spi_host_gigadevice256Mb_flash_test",
    srcs = ["spi_host_gigadevice256Mb_flash_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:spi_host_flash_test_impl",
    ],
)

opentitan_test(
    name = "spi_host_gigadevice1Gb_flash_test",
    srcs = ["spi_host_gigadevice1Gb_flash_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:spi_host_flash_test_impl",
    ],
)

opentitan_test(
    name = "spi_host_micron512Mb_flash_test",
    srcs = ["spi_host_micron512Mb_flash_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:pinmux",
        "//sw/device/lib/dif:spi_host",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:spi_device_testutils",
        "//sw/device/lib/testing:spi_flash_testutils",
        "//sw/device/lib/testing:spi_host_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/tests:spi_host_flash_test_impl",
    ],
)

opentitan_test(
    name = "i2c_host_accelerometer_test",
    srcs = ["i2c_host_accelerometer_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_ambient_light_detector_test",
    srcs = ["i2c_host_ambient_light_detector_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_hdc1080_humidity_temp_test",
    srcs = ["i2c_host_hdc1080_humidity_temp_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_clock_stretching_test",
    srcs = ["i2c_host_clock_stretching_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "i2c_host_compass_test",
    srcs = ["i2c_host_compass_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:i2c",
        "//sw/device/lib/dif:rstmgr",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:i2c_testutils",
        "//sw/device/lib/testing:rv_core_ibex_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "i2c_host_eeprom_test",
    srcs = ["i2c_host_eeprom_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_fram_test",
    srcs = ["i2c_host_fram_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_gas_sensor_test",
    srcs = ["i2c_host_gas_sensor_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_power_monitor_test",
    srcs = ["i2c_host_power_monitor_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
    name = "i2c_host_irq_test",
    srcs = ["i2c_host_irq_test.c"],
    cw310 = cw310_params(
        tags = [
            "bob",
            "manual",
        ],  # Requires the BoB in CI.
    ),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
    },
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
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
