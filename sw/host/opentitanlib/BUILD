# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("//third_party/cargo:crates.bzl", "all_crate_deps")

package(default_visibility = ["//visibility:public"])

rust_library(
    name = "opentitanlib",
    srcs = [
        "src/app/command.rs",
        "src/app/conf.rs",
        "src/app/mod.rs",
        "src/backend/cw310.rs",
        "src/backend/hyperdebug.rs",
        "src/backend/mod.rs",
        "src/backend/ultradebug.rs",
        "src/backend/verilator.rs",
        "src/bootstrap/legacy.rs",
        "src/bootstrap/mod.rs",
        "src/bootstrap/primitive.rs",
        "src/bootstrap/rescue.rs",
        "src/crypto/mod.rs",
        "src/crypto/sha256.rs",
        "src/io/gpio.rs",
        "src/io/i2c.rs",
        "src/io/mod.rs",
        "src/io/spi.rs",
        "src/io/uart.rs",
        "src/lib.rs",
        "src/otp/lc_state.rs",
        "src/otp/mod.rs",
        "src/otp/num_de.rs",
        "src/otp/otp.rs",
        "src/otp/otp_img.rs",
        "src/otp/otp_mmap.rs",
        "src/otp/vmem_serialize.rs",
        "src/spiflash/flash.rs",
        "src/spiflash/mod.rs",
        "src/spiflash/sfdp.rs",
        "src/transport/common/mod.rs",
        "src/transport/common/uart.rs",
        "src/transport/cw310/gpio.rs",
        "src/transport/cw310/mod.rs",
        "src/transport/cw310/spi.rs",
        "src/transport/cw310/usb.rs",
        "src/transport/errors.rs",
        "src/transport/hyperdebug/c2d2.rs",
        "src/transport/hyperdebug/gpio.rs",
        "src/transport/hyperdebug/i2c.rs",
        "src/transport/hyperdebug/mod.rs",
        "src/transport/hyperdebug/spi.rs",
        "src/transport/mod.rs",
        "src/transport/ultradebug/gpio.rs",
        "src/transport/ultradebug/mod.rs",
        "src/transport/ultradebug/mpsse.rs",
        "src/transport/ultradebug/spi.rs",
        "src/transport/ultradebug/uart.rs",
        "src/transport/verilator/mod.rs",
        "src/transport/verilator/subprocess.rs",
        "src/transport/verilator/transport.rs",
        "src/transport/verilator/uart.rs",
        "src/util/bigint.rs",
        "src/util/bitfield.rs",
        "src/util/file.rs",
        "src/util/image.rs",
        "src/util/mod.rs",
        "src/util/parse_int.rs",
        "src/util/present.rs",
        "src/util/usb.rs",
        "src/util/voltage.rs",
    ],
    proc_macro_deps = [
        "//sw/host/opentitanlib/opentitantool_derive",
    ],
    deps = [
        "@mundane//:mundane",
    ] + all_crate_deps(),
)

rust_test(
    name = "opentitanlib_test",
    compile_data = [
        "src/bootstrap/simple.bin",
        "src/spiflash/SFDP_MX66L1G.bin",
    ],
    crate = ":opentitanlib",
    data = [
        "src/otp/testdata/lc_ctrl_state.hjson",
        "src/otp/testdata/otp_ctrl_img_dev.hjson",
        "src/otp/testdata/otp_ctrl_mmap.hjson",
        "src/otp/testdata/output.vmem",
        "src/util/testdata/hello.txt",
        "src/util/testdata/world.txt",
    ],
)
