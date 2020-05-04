//! Device specific configuration.

pub struct DeviceConfig<'a> {
    pub name: &'a str,
    pub chip_freq: u32,
    pub uart_baudrate: u32,
}

// This is also a default case, when no device is specified.
#[cfg(any(feature = "device_fpga", not(feature = "device_specified")))]
pub const DEVICE_CONFIG: DeviceConfig = DeviceConfig {
    name: &"device_fpga",
    chip_freq: 50_000_000,
    uart_baudrate: 230400,
};

#[cfg(feature = "device_verilator")]
pub const DEVICE_CONFIG: DeviceConfig = DeviceConfig {
    name: &"device_verilator",
    chip_freq: 500_000,
    uart_baudrate: 9600,
};
