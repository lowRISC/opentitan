# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_cw310",
)
load("@bazel_skylib//lib:dicts.bzl", "dicts")

package(default_visibility = ["//visibility:public"])

# A custom execution environment, which uses the same attributes as the CW310
# SiVal ROM EXT execution environment, but uses the base universal bitstream
# & interface for the CW310 as opposed to the hyperdebug variants, due to the
# PMOD tests requiring the PMOD pins that are not available with hyperdebug.
fpga_cw310(
    name = "top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper",
    testonly = True,
    base = "//hw/top_earlgrey:fpga_cw310_sival_rom_ext",
    # Override the hyperdebug bitstream, interface, and OTP & ROM MMIs.
    base_bitstream = "//hw/bitstream:bitstream",
    exec_env = "fpga_cw310_sival_rom_ext_no_hyper",
    mmi = "//hw/bitstream:cw310_mmi",
    param = {
        "interface": "cw310",
        "exit_success": DEFAULT_TEST_SUCCESS_MSG,
        "exit_failure": DEFAULT_TEST_FAILURE_MSG,
        "assemble": "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a}",
    },
    visibility = ["//visibility:private"],
)

opentitan_test(
    name = "spi_host_macronix1Gb_flash_test",
    srcs = ["spi_host_macronix1Gb_flash_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    name = "spi_host_macronix128Mb_flash_test",
    srcs = ["spi_host_macronix128Mb_flash_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    name = "spi_host_issi256Mb_flash_test",
    srcs = ["spi_host_issi256Mb_flash_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    name = "spi_host_winbond1Gb_flash_test",
    srcs = ["spi_host_winbond1Gb_flash_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    deps = [
        "//hw/top/dt",
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
    name = "i2c_host_ambient_light_detector_test",
    srcs = ["i2c_host_ambient_light_detector_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
    name = "i2c_host_hdc1080_humidity_temp_test",
    srcs = ["i2c_host_hdc1080_humidity_temp_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
    name = "i2c_host_clock_stretching_test",
    srcs = ["i2c_host_clock_stretching_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "i2c_host_compass_test",
    srcs = ["i2c_host_compass_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
    name = "i2c_host_fram_test",
    srcs = ["i2c_host_fram_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
    ),
    # This test can take > 40 minutes, so mark it manual as it shouldn't run
    # in CI/nightlies.
    verilator = verilator_params(tags = ["manual"]),
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
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
    name = "i2c_host_power_monitor_test",
    srcs = ["i2c_host_power_monitor_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
    name = "i2c_host_irq_test",
    srcs = ["i2c_host_irq_test.c"],
    exec_env = dicts.add(
        EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
        {":top_earlgrey_fpga_cw310_sival_rom_ext_no_hyper": None},
    ),
    fpga = fpga_params(
        tags = [
            "manual",
            "pmod",
        ],  # Requires the PMOD::BoB.
    ),
    silicon = silicon_params(
        tags = ["pmod"],  # Requires the PMOD::BoB.
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
        "//sw/device/lib/testing:rv_plic_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
