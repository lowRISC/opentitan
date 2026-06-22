# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")
load("@bazel_skylib//rules:common_settings.bzl", "bool_flag")
load("//rules:ujson.bzl", "ujson_rust")

package(default_visibility = ["//visibility:public"])

ujson_rust(
    name = "e2e_command",
    srcs = ["//sw/device/lib/testing/json:command"],
    defines = ["opentitanlib=crate"],
)

ujson_rust(
    name = "gpio",
    srcs = ["//sw/device/lib/testing/json:gpio"],
    defines = ["opentitanlib=crate"],
)

ujson_rust(
    name = "i2c_target",
    srcs = ["//sw/device/lib/testing/json:i2c_target"],
    defines = ["opentitanlib=crate"],
)

ujson_rust(
    name = "mem",
    srcs = ["//sw/device/lib/testing/json:mem"],
    defines = ["opentitanlib=crate"],
)

ujson_rust(
    name = "pinmux_config",
    srcs = ["//sw/device/lib/testing/json:pinmux_config"],
    defines = ["opentitanlib=crate"],
)

ujson_rust(
    name = "spi_passthru",
    srcs = ["//sw/device/lib/testing/json:spi_passthru"],
    defines = ["opentitanlib=crate"],
)

ujson_rust(
    name = "ottf",
    srcs = ["//sw/device/lib/testing/json:ottf"],
    defines = ["opentitanlib=crate"],
)

# Define the core sub-crate.
rust_library(
    name = "opentitanlib_core",
    srcs = [
        "src/core_lib.rs",
        "src/crypto/ecdsa.rs",
        "src/crypto/mod.rs",
        "src/crypto/rsa.rs",
        "src/crypto/sha256.rs",
        "src/crypto/spx.rs",
        "src/io/bootstrap_types.rs",
        "src/io/capabilities.rs",
        "src/io/console.rs",
        "src/io/console/broadcast.rs",
        "src/io/console/buf.rs",
        "src/io/console/coverage.rs",
        "src/io/console/coverage_test.rs",
        "src/io/console/ext.rs",
        "src/io/console/logged.rs",
        "src/io/eeprom.rs",
        "src/io/emu.rs",
        "src/io/errors.rs",
        "src/io/gpio.rs",
        "src/io/i2c.rs",
        "src/io/ioexpander.rs",
        "src/io/jtag.rs",
        "src/io/middleware.rs",
        "src/io/mod.rs",
        "src/io/spi.rs",
        "src/io/uart/flow.rs",
        "src/io/uart/mod.rs",
        "src/io/uart/serial.rs",
        "src/io/usb/desc.rs",
        "src/io/usb/mod.rs",
        "src/transport/common/usb.rs",
        "src/transport_core.rs",
        "src/util/bigint.rs",
        "src/util/bitbang.rs",
        "src/util/file.rs",
        "src/util/fs.rs",
        "src/util/hexdump.rs",
        "src/util/mod.rs",
        "src/util/num_de.rs",
        "src/util/parse_int.rs",
        "src/util/poll.rs",
        "src/util/present.rs",
        "src/util/printer.rs",
        "src/util/raw_tty.rs",
        "src/util/regex.rs",
        "src/util/rom_detect.rs",
        "src/util/runtime.rs",
        "src/util/serde.rs",
        "src/util/serializable_error.rs",
        "src/util/status.rs",
        "src/util/testing.rs",
        "src/util/usr_access.rs",
        "src/util/vcd.rs",
        "src/util/vmem/mod.rs",
        "src/util/vmem/parser.rs",
        "src/util/voltage.rs",
    ],
    crate_name = "opentitanlib_core",
    crate_root = "src/core_lib.rs",
    deps = [
        "//sw/host/opentitanlib/bindgen",
        "//sw/host/opentitanlib/util",
        "//sw/host/ot_hal",
        "//sw/host/sphincsplus",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:bitflags",
        "@crate_index//:byteorder",
        "@crate_index//:chrono",
        "@crate_index//:clap",
        "@crate_index//:crc",
        "@crate_index//:derive_more",
        "@crate_index//:ecdsa",
        "@crate_index//:erased-serde",
        "@crate_index//:hex",
        "@crate_index//:humantime",
        "@crate_index//:humantime-serde",
        "@crate_index//:inventory",
        "@crate_index//:log",
        "@crate_index//:memchr",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:num-traits",
        "@crate_index//:object",
        "@crate_index//:p256",
        "@crate_index//:pem-rfc7468",
        "@crate_index//:rand",
        "@crate_index//:regex",
        "@crate_index//:rsa",
        "@crate_index//:rusb",
        "@crate_index//:rustix",
        "@crate_index//:scopeguard",
        "@crate_index//:serde",
        "@crate_index//:serde_bytes",
        "@crate_index//:serde_json",
        "@crate_index//:serialport",
        "@crate_index//:sha2",
        "@crate_index//:shellwords",
        "@crate_index//:strum",
        "@crate_index//:tempfile",
        "@crate_index//:thiserror",
        "@crate_index//:tokio",
        "@crate_index//:typetag",
        "@crate_index//:zerocopy",
        "@lowrisc_serde_annotate//serde_annotate",
    ],
)

# Define the chip sub-crate.
rust_library(
    name = "opentitanlib_chip",
    srcs = [
        "src/chip/boolean.rs",
        "src/chip/boot_log.rs",
        "src/chip/boot_svc.rs",
        "src/chip/device_id.rs",
        "src/chip/helper.rs",
        "src/chip/mod.rs",
        "src/chip/rom_error.rs",
        "src/chip_lib.rs",
        "src/otp/alert_handler.rs",
        "src/otp/alert_handler_regs.rs",
        "src/otp/lc_state.rs",
        "src/otp/mod.rs",
        "src/otp/otp_img.rs",
        "src/ownership/application_key.rs",
        "src/ownership/flash.rs",
        "src/ownership/flash_info.rs",
        "src/ownership/isfb.rs",
        "src/ownership/misc.rs",
        "src/ownership/mod.rs",
        "src/ownership/owner.rs",
        "src/ownership/rescue.rs",
        "src/ownership/signature.rs",
    ],
    compile_data = [
        "//sw/host/opentitanlib/bindgen:rom_error_enum",
    ],
    crate_name = "opentitanlib_chip",
    crate_root = "src/chip_lib.rs",
    rustc_env = {
        "rom_error_enum": "$(location //sw/host/opentitanlib/bindgen:rom_error_enum)",
    },
    deps = [
        ":opentitanlib_core",
        "//sw/host/opentitanlib/bindgen",
        "//sw/host/ot_hal",
        "//sw/host/sphincsplus",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:byteorder",
        "@crate_index//:clap",
        "@crate_index//:crc",
        "@crate_index//:deser-hjson",
        "@crate_index//:log",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:p256",
        "@crate_index//:serde",
        "@crate_index//:serde_bytes",
        "@crate_index//:serde_json",
        "@crate_index//:sha2",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
        "@lowrisc_serde_annotate//serde_annotate",
    ],
)

# Define the debug sub-crate.
rust_library(
    name = "opentitanlib_debug",
    srcs = [
        "src/debug/dmi.rs",
        "src/debug/elf_debugger.rs",
        "src/debug/mod.rs",
        "src/debug/openocd.rs",
        "src/debug_lib.rs",
    ],
    compile_data = [
        "//util/openocd/target:lowrisc-earlgrey.cfg",
        "//util/openocd/target:lowrisc-earlgrey-lc.cfg",
    ],
    crate_name = "opentitanlib_debug",
    crate_root = "src/debug_lib.rs",
    rustc_env = {
        "openocd_riscv_target_cfg": "$(location //util/openocd/target:lowrisc-earlgrey.cfg)",
        "openocd_lc_target_cfg": "$(location //util/openocd/target:lowrisc-earlgrey-lc.cfg)",
    },
    deps = [
        ":opentitanlib_core",
        "//sw/host/ot_hal",
        "@crate_index//:anyhow",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:regex",
        "@crate_index//:rustix",
        "@crate_index//:scopeguard",
        "@crate_index//:serde",
        "@crate_index//:thiserror",
        "@crate_index//:typetag",
    ],
)

# Define the app sub-crate.
rust_library(
    name = "opentitanlib_app",
    srcs = [
        "src/app/command.rs",
        "src/app/config/mod.rs",
        "src/app/config/structs.rs",
        "src/app/gpio.rs",
        "src/app/i2c.rs",
        "src/app/mod.rs",
        "src/app/spi.rs",
        "src/app_lib.rs",
        "src/transport/common/fpga.rs",
        "src/transport/ioexpander/mod.rs",
        "src/transport/ioexpander/sx1503.rs",
    ],
    crate_name = "opentitanlib_app",
    crate_root = "src/app_lib.rs",
    proc_macro_deps = [
        "//sw/host/opentitanlib/opentitantool_derive",
    ],
    deps = [
        ":opentitanlib_chip",
        ":opentitanlib_core",
        ":opentitanlib_debug",
        "//sw/host/opentitanlib/bindgen",
        "//sw/host/ot_hal",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:deser-hjson",
        "@crate_index//:directories",
        "@crate_index//:erased-serde",
        "@crate_index//:hex",
        "@crate_index//:humantime",
        "@crate_index//:humantime-serde",
        "@crate_index//:indicatif",
        "@crate_index//:inventory",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:serialport",
        "@crate_index//:shellwords",
        "@crate_index//:thiserror",
        "@lowrisc_serde_annotate//serde_annotate",
    ],
)

# Define the image sub-crate.
rust_library(
    name = "opentitanlib_image",
    srcs = [
        "src/image/image.rs",
        "src/image/manifest.rs",
        "src/image/manifest_def.rs",
        "src/image/manifest_ext.rs",
        "src/image/mod.rs",
        "src/image_lib.rs",
    ],
    crate_name = "opentitanlib_image",
    crate_root = "src/image_lib.rs",
    deps = [
        ":opentitanlib_chip",
        ":opentitanlib_core",
        "//sw/host/sphincsplus",
        "@crate_index//:anyhow",
        "@crate_index//:byteorder",
        "@crate_index//:clap",
        "@crate_index//:deser-hjson",
        "@crate_index//:log",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:serde",
        "@crate_index//:thiserror",
        "@crate_index//:zerocopy",
        "@lowrisc_serde_annotate//serde_annotate",
    ],
)

# Define the protocols sub-crate.
rust_library(
    name = "opentitanlib_protocols",
    srcs = [
        "src/bootstrap/eeprom.rs",
        "src/bootstrap/legacy.rs",
        "src/bootstrap/legacy_rescue.rs",
        "src/bootstrap/mod.rs",
        "src/bootstrap/primitive.rs",
        "src/console/mod.rs",
        "src/console/spi.rs",
        "src/protocols_lib.rs",
        "src/rescue/dfu.rs",
        "src/rescue/mod.rs",
        "src/rescue/serial.rs",
        "src/rescue/spidfu.rs",
        "src/rescue/usbdfu.rs",
        "src/rescue/xmodem.rs",
        "src/spiflash/flash.rs",
        "src/spiflash/mod.rs",
        "src/spiflash/sfdp.rs",
        "src/tpm/access.rs",
        "src/tpm/driver.rs",
        "src/tpm/mod.rs",
        "src/tpm/status.rs",
        "src/uart/console.rs",
        "src/uart/mod.rs",
    ],
    crate_name = "opentitanlib_protocols",
    crate_root = "src/protocols_lib.rs",
    deps = [
        ":opentitanlib_app",
        ":opentitanlib_chip",
        ":opentitanlib_core",
        "@crate_index//:anyhow",
        "@crate_index//:bitflags",
        "@crate_index//:byteorder",
        "@crate_index//:clap",
        "@crate_index//:humantime",
        "@crate_index//:humantime-serde",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:serde",
        "@crate_index//:sha2",
        "@crate_index//:strum",
        "@crate_index//:thiserror",
        "@crate_index//:tokio",
        "@crate_index//:typetag",
        "@crate_index//:zerocopy",
        "@lowrisc_serde_annotate//serde_annotate",
    ],
)

# Define the backend sub-crate.
rust_library(
    name = "opentitanlib_backend",
    srcs = [
        "src/backend/mod.rs",
        "src/backend_lib.rs",
    ],
    crate_name = "opentitanlib_backend",
    crate_root = "src/backend_lib.rs",
    deps = [
        ":opentitanlib_app",
        ":opentitanlib_core",
        "@crate_index//:anyhow",
        "@crate_index//:clap",
        "@crate_index//:inventory",
        "@crate_index//:thiserror",
    ],
)

# Define the test_utils sub-crate.
rust_library(
    name = "opentitanlib_test_utils",
    srcs = [
        "src/test_utils/bitbanging/i2c.rs",
        "src/test_utils/bitbanging/mod.rs",
        "src/test_utils/bitbanging/pwm.rs",
        "src/test_utils/bitbanging/spi.rs",
        "src/test_utils/bitbanging/uart.rs",
        "src/test_utils/bitbanging/uart_rx_sampling.rs",
        "src/test_utils/bootstrap.rs",
        "src/test_utils/crashdump.rs",
        "src/test_utils/e2e_command.rs",
        "src/test_utils/epmp.rs",
        "src/test_utils/gpio.rs",
        "src/test_utils/gpio_monitor.rs",
        "src/test_utils/i2c_target.rs",
        "src/test_utils/init.rs",
        "src/test_utils/lc.rs",
        "src/test_utils/lc_transition.rs",
        "src/test_utils/load_bitstream.rs",
        "src/test_utils/load_sram_program.rs",
        "src/test_utils/mem.rs",
        "src/test_utils/mod.rs",
        "src/test_utils/object.rs",
        "src/test_utils/otp_ctrl.rs",
        "src/test_utils/poll.rs",
        "src/test_utils/rpc.rs",
        "src/test_utils/spi_passthru.rs",
        "src/test_utils/status.rs",
        "src/test_utils/test_status.rs",
        "src/test_utils_lib.rs",
    ] + select({
        "//sw/device:is_english_breakfast": [],
        "//conditions:default": [
            "src/test_utils/extclk.rs",
            "src/test_utils/pinmux_config.rs",
        ],
    }),
    compile_data = [
        ":gpio",
        ":i2c_target",
        ":mem",
        ":e2e_command",
        ":pinmux_config",
        ":spi_passthru",
        ":ottf",
        "//sw/host/opentitanlib/bindgen:rom_error_enum",
    ],
    crate_features = select({
        "//sw/device:is_english_breakfast": ["english_breakfast"],
        "//conditions:default": [],
    }),
    crate_name = "opentitanlib_test_utils",
    crate_root = "src/test_utils_lib.rs",
    rustc_env = {
        "e2e_command": "$(location :e2e_command)",
        "gpio": "$(location :gpio)",
        "i2c_target": "$(location :i2c_target)",
        "mem": "$(location :mem)",
        "pinmux_config": "$(location :pinmux_config)",
        "rom_error_enum": "$(location //sw/host/opentitanlib/bindgen:rom_error_enum)",
        "spi_passthru": "$(location :spi_passthru)",
        "ottf": "$(location :ottf)",
    },
    deps = [
        ":opentitanlib_app",
        ":opentitanlib_backend",
        ":opentitanlib_chip",
        ":opentitanlib_core",
        ":opentitanlib_debug",
        ":opentitanlib_image",
        ":opentitanlib_protocols",
        "//sw/host/opentitanlib/bindgen",
        "//sw/host/opentitanlib/util",
        "//sw/host/ot_hal",
        "//sw/host/ot_hal/bindgen",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:byteorder",
        "@crate_index//:clap",
        "@crate_index//:crc",
        "@crate_index//:directories",
        "@crate_index//:env_logger",
        "@crate_index//:erased-serde",
        "@crate_index//:humantime",
        "@crate_index//:log",
        "@crate_index//:object",
        "@crate_index//:regex",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:serialport",
        "@crate_index//:shellwords",
        "@crate_index//:thiserror",
        "@crate_index//:typetag",
    ],
)

# This is the catch-all "everything" crate.
# Before adding things here, consider if it can be made a separate crate instead.
# This should eventually be break down into multiple smaller crates.
rust_library(
    name = "opentitanlib_base",
    srcs = [
        "src/lib.rs",
        "src/transport/common/mod.rs",
        "src/transport/mod.rs",
    ],
    crate_name = "opentitanlib",
    deps = [
        ":opentitanlib_app",
        ":opentitanlib_backend",
        ":opentitanlib_chip",
        ":opentitanlib_core",
        ":opentitanlib_debug",
        ":opentitanlib_image",
        ":opentitanlib_protocols",
        ":opentitanlib_test_utils",
        "//sw/host/opentitanlib/bindgen",
        "//sw/host/opentitanlib/util",
        "//sw/host/ot_hal",
        "//sw/host/ot_hal/bindgen",
        "//sw/host/sphincsplus",
        "@crate_index//:anyhow",
        "@crate_index//:arrayvec",
        "@crate_index//:bitflags",
        "@crate_index//:byteorder",
        "@crate_index//:chrono",
        "@crate_index//:clap",
        "@crate_index//:crc",
        "@crate_index//:derive_more",
        "@crate_index//:deser-hjson",
        "@crate_index//:directories",
        "@crate_index//:ecdsa",
        "@crate_index//:env_logger",
        "@crate_index//:erased-serde",
        "@crate_index//:hex",
        "@crate_index//:humantime",
        "@crate_index//:humantime-serde",
        "@crate_index//:indicatif",
        "@crate_index//:inventory",
        "@crate_index//:log",
        "@crate_index//:memchr",
        "@crate_index//:num-bigint-dig",
        "@crate_index//:num-traits",
        "@crate_index//:object",
        "@crate_index//:p256",
        "@crate_index//:pem-rfc7468",
        "@crate_index//:rand",
        "@crate_index//:regex",
        "@crate_index//:rsa",
        "@crate_index//:rusb",
        "@crate_index//:rustix",
        "@crate_index//:scopeguard",
        "@crate_index//:serde",
        "@crate_index//:serde_bytes",
        "@crate_index//:serde_json",
        "@crate_index//:serialport",
        "@crate_index//:sha2",
        "@crate_index//:shellwords",
        "@crate_index//:strum",
        "@crate_index//:tempfile",
        "@crate_index//:thiserror",
        "@crate_index//:tokio",
        "@crate_index//:typetag",
        "@crate_index//:zerocopy",
        "@lowrisc_serde_annotate//serde_annotate",
    ],
)

# To avoid having all existing `opentitanlib` to carry dependency of individual splitted crates,
# re-export everything under the original `opentitanlib` name.

_TRANSPORTS = [
    "chipwhisperer",
    "dediprog",
    "ftdi",
    "hyperdebug",
    "proxy",
    "ti50emulator",
    "verilator",
]

[
    bool_flag(
        name = "transport_{}".format(t),
        build_setting_default = True,
    )
    for t in _TRANSPORTS
]

[
    config_setting(
        name = "transport_{}_enabled".format(t),
        flag_values = {":transport_{}".format(t): "True"},
    )
    for t in _TRANSPORTS
]

_TRANSPORT_DEPS = select({
    ":transport_chipwhisperer_enabled": ["//sw/host/ot_transports/chipwhisperer"],
    "//conditions:default": [],
}) + select({
    ":transport_dediprog_enabled": ["//sw/host/ot_transports/dediprog"],
    "//conditions:default": [],
}) + select({
    ":transport_ftdi_enabled": ["//sw/host/ot_transports/ftdi"],
    "//conditions:default": [],
}) + select({
    ":transport_hyperdebug_enabled": ["//sw/host/ot_transports/hyperdebug"],
    "//conditions:default": [],
}) + select({
    ":transport_proxy_enabled": ["//sw/host/ot_transports/proxy"],
    "//conditions:default": [],
}) + select({
    ":transport_ti50emulator_enabled": ["//sw/host/ot_transports/ti50emulator"],
    "//conditions:default": [],
}) + select({
    ":transport_verilator_enabled": ["//sw/host/ot_transports/verilator"],
    "//conditions:default": [],
})

_TRANSPORT_FEATURES = select({
    ":transport_chipwhisperer_enabled": ["chipwhisperer"],
    "//conditions:default": [],
}) + select({
    ":transport_dediprog_enabled": ["dediprog"],
    "//conditions:default": [],
}) + select({
    ":transport_ftdi_enabled": ["ftdi"],
    "//conditions:default": [],
}) + select({
    ":transport_hyperdebug_enabled": ["hyperdebug"],
    "//conditions:default": [],
}) + select({
    ":transport_proxy_enabled": ["proxy"],
    "//conditions:default": [],
}) + select({
    ":transport_ti50emulator_enabled": ["ti50emulator"],
    "//conditions:default": [],
}) + select({
    ":transport_verilator_enabled": ["verilator"],
    "//conditions:default": [],
})

rust_library(
    name = "opentitanlib",
    srcs = [
        "reexport.rs",
    ],
    aliases = {
        ":opentitanlib_base": "opentitanlib_base",
    },
    crate_features = _TRANSPORT_FEATURES,
    deps = [
        ":opentitanlib_base",
    ] + _TRANSPORT_DEPS,
)

test_suite(
    name = "opentitanlib_test",
    tests = [
        ":opentitanlib_chip_test",
        ":opentitanlib_core_test",
        ":opentitanlib_image_test",
        ":opentitanlib_protocols_test",
    ],
)

rust_test(
    name = "opentitanlib_chip_test",
    crate = ":opentitanlib_chip",
    data = glob(["testdata/**"]),
    env = {
        "TESTDATA": "$(rootpath testdata/otp/lc_ctrl_state.hjson)",
    },
    deps = [
        "@crate_index//:hex",
    ],
)

rust_test(
    name = "opentitanlib_core_test",
    crate = ":opentitanlib_core",
    deps = [
        "@crate_index//:deser-hjson",
    ],
)

rust_test(
    name = "opentitanlib_image_test",
    crate = ":opentitanlib_image",
    data = glob(["testdata/**"]),
    env = {
        "RUST_MIN_STACK": "4194304",
        "TESTDATA": "$(rootpath testdata/otp/lc_ctrl_state.hjson)",
    },
)

rust_test(
    name = "opentitanlib_protocols_test",
    compile_data = [
        "src/bootstrap/simple.bin",
        "src/spiflash/SFDP_MX66L1G.bin",
    ],
    crate = ":opentitanlib_protocols",
    deps = [
        "@crate_index//:hex",
    ],
)

rust_doc(
    name = "opentitanlib_doc",
    crate = ":opentitanlib_base",
)

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]),
)
