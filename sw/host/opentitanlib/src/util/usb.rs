// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Context, Result};
use rusb;
use std::time::Duration;

use crate::transport::TransportError;

/// The `UsbBackend` provides low-level USB access to debugging devices.
pub struct UsbBackend {
    device: rusb::Device<rusb::GlobalContext>,
    handle: rusb::DeviceHandle<rusb::GlobalContext>,
    serial_number: String,
    timeout: Duration,
}

impl UsbBackend {
    /// Scan the USB bus for a device matching VID/PID, and optionally also matching a serial
    /// number.
    pub fn scan(
        usb_vid: u16,
        usb_pid: u16,
        usb_serial: Option<&str>,
    ) -> Result<Vec<(rusb::Device<rusb::GlobalContext>, String)>> {
        let mut devices = Vec::new();
        let mut deferred_log_messages = Vec::new();
        for device in rusb::devices().context("USB error")?.iter() {
            let descriptor = match device.device_descriptor() {
                Ok(desc) => desc,
                Err(e) => {
                    deferred_log_messages.push(format!(
                        "Could not read device descriptor for device at bus={} address={}: {}",
                        device.bus_number(),
                        device.address(),
                        e,
                    ));
                    continue;
                }
            };
            if descriptor.vendor_id() != usb_vid {
                continue;
            }
            if descriptor.product_id() != usb_pid {
                continue;
            }
            let handle = match device.open() {
                Ok(handle) => handle,
                Err(e) => {
                    deferred_log_messages.push(format!(
                        "Could not open device at bus={} address={}: {}",
                        device.bus_number(),
                        device.address(),
                        e,
                    ));
                    continue;
                }
            };
            let serial_number = match handle.read_serial_number_string_ascii(&descriptor) {
                Ok(sn) => sn,
                Err(e) => {
                    deferred_log_messages.push(format!(
                        "Could not read serial number from device at bus={} address={}: {}",
                        device.bus_number(),
                        device.address(),
                        e,
                    ));
                    continue;
                }
            };
            if let Some(sn) = &usb_serial {
                if &serial_number != sn {
                    continue;
                }
            }
            devices.push((device, serial_number));
        }

        // We expect to find exactly one matching device. If that happens, the
        // deferred log messages are unimportant. Otherwise, one of the messages
        // may yield some insight into what went wrong, so they should be logged
        // at a higher priority.
        let severity = match devices.len() {
            1 => log::Level::Info,
            _ => log::Level::Error,
        };
        for s in deferred_log_messages {
            log::log!(severity, "{}", s);
        }

        Ok(devices)
    }

    /// Create a new UsbBackend.
    pub fn new(usb_vid: u16, usb_pid: u16, usb_serial: Option<&str>) -> Result<Self> {
        let mut devices = UsbBackend::scan(usb_vid, usb_pid, usb_serial)?;
        ensure!(!devices.is_empty(), TransportError::NoDevice);
        ensure!(devices.len() == 1, TransportError::MultipleDevices);

        let (device, serial_number) = devices.remove(0);
        Ok(UsbBackend {
            handle: device.open().context("USB open error")?,
            device,
            serial_number,
            timeout: Duration::from_millis(500),
        })
    }

    pub fn get_vendor_id(&self) -> u16 {
        self.device.device_descriptor().unwrap().vendor_id()
    }

    pub fn get_product_id(&self) -> u16 {
        self.device.device_descriptor().unwrap().product_id()
    }

    /// Gets the usb serial number of the device.
    pub fn get_serial_number(&self) -> &str {
        self.serial_number.as_str()
    }

    pub fn set_active_configuration(&mut self, config: u8) -> Result<()> {
        self.handle
            .set_active_configuration(config)
            .context("USB error")
    }

    pub fn claim_interface(&mut self, iface: u8) -> Result<()> {
        self.handle.claim_interface(iface).context("USB error")
    }

    //
    // Enumerating interfaces of the USB device.  The methods below leak rusb data structures,
    // and may have to be refactored, when we convert UsbDevice into a trait, and want to
    // support mocked implementations.
    //

    pub fn active_config_descriptor(&self) -> Result<rusb::ConfigDescriptor> {
        self.device.active_config_descriptor().context("USB error")
    }

    pub fn bus_number(&self) -> u8 {
        self.device.bus_number()
    }

    pub fn port_numbers(&self) -> Result<Vec<u8>> {
        self.device.port_numbers().context("USB error")
    }

    pub fn read_string_descriptor_ascii(&self, idx: u8) -> Result<String> {
        self.handle
            .read_string_descriptor_ascii(idx)
            .context("USB error")
    }

    //
    // Sending and receiving data, the below methods provide a nice interface.
    //

    /// Issue a USB control request with optional host-to-device data.
    pub fn write_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &[u8],
    ) -> Result<usize> {
        self.handle
            .write_control(request_type, request, value, index, buf, self.timeout)
            .context("USB error")
    }

    /// Issue a USB control request with optional device-to-host data.
    pub fn read_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &mut [u8],
    ) -> Result<usize> {
        self.handle
            .read_control(request_type, request, value, index, buf, self.timeout)
            .context("USB error")
    }

    /// Read bulk data bytes to given USB endpoint.
    pub fn read_bulk(&self, endpoint: u8, data: &mut [u8]) -> Result<usize> {
        let len = self
            .handle
            .read_bulk(endpoint, data, self.timeout)
            .context("USB error")?;
        Ok(len)
    }

    /// Read bulk data bytes to given USB endpoint.
    pub fn read_bulk_timeout(
        &self,
        endpoint: u8,
        data: &mut [u8],
        timeout: Duration,
    ) -> Result<usize> {
        let len = self
            .handle
            .read_bulk(endpoint, data, timeout)
            .context("USB error")?;
        Ok(len)
    }

    /// Write bulk data bytes to given USB endpoint.
    pub fn write_bulk(&self, endpoint: u8, data: &[u8]) -> Result<usize> {
        let len = self
            .handle
            .write_bulk(endpoint, data, self.timeout)
            .context("USB error")?;
        Ok(len)
    }
}
