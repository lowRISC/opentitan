# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_doc", "rust_library", "rust_test")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "hyperdebug",
    srcs = [
        "src/c2d2.rs",
        "src/dfu.rs",
        "src/gpio.rs",
        "src/i2c.rs",
        "src/lib.rs",
        "src/servo_micro.rs",
        "src/spi.rs",
        "src/ti50.rs",
        "src/uart.rs",
    ],
    compile_data = glob(["config/*.json5"]) + [
        "@hyperdebug_firmware//:hyperdebug/ec.bin",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
    ],
    crate_features = [
        "include_hyperdebug_firmware",
    ],
    crate_name = "ot_transport_hyperdebug",
    rustc_env = {
        "hyperdebug_firmware": "$(location @hyperdebug_firmware//:hyperdebug/ec.bin)",
        "openocd_cmsis_dap_adapter_cfg": "$(location //third_party/openocd:jtag_cmsis_dap_adapter_cfg)",
    },
    deps = [
        "//sw/host/opentitanlib:opentitanlib_base",
        "//sw/host/ot_transports/chipwhisperer",
        "@crate_index//:anyhow",
        "@crate_index//:byteorder",
        "@crate_index//:clap",
        "@crate_index//:erased-serde",
        "@crate_index//:log",
        "@crate_index//:regex",
        "@crate_index//:rusb",
        "@crate_index//:serialport",
        "@crate_index//:zerocopy",
    ],
)

rust_doc(
    name = "hyperdebug_doc",
    crate = ":hyperdebug",
)

rust_test(
    name = "hyperdebug_test",
    crate = ":hyperdebug",
)
