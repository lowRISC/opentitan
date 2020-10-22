// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Chip configuration based on the target device.
pub struct DeviceConfig<'a> {
    pub name: &'a str,
    pub chip_freq: u32,
    pub uart_baudrate: u32,
}

// This is also a default case, when no device is specified.
#[cfg(any(feature = "fpga_nexysvideo", not(feature = "device_specified")))]
pub const DEVICE_CONFIG: DeviceConfig = DeviceConfig {
    name: &"fpga_nexysvideo",
    chip_freq: 10_000_000,
    uart_baudrate: 115200,
};

#[cfg(feature = "sim_verilator")]
pub const DEVICE_CONFIG: DeviceConfig = DeviceConfig {
    name: &"sim_verilator",
    chip_freq: 500_000,
    uart_baudrate: 9600,
};
