// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result, ensure};
use rusb::{self, UsbContext};
use std::time::{Duration, Instant};

use crate::transport::TransportError;

/// The `UsbBackend` provides low-level USB access to debugging devices.
pub struct UsbBackend {
    device: rusb::Device<rusb::Context>,
    handle: rusb::DeviceHandle<rusb::Context>,
    serial_number: String,
    timeout: Duration,
}

impl UsbBackend {
    /// Scan the USB bus for a device matching VID/PID, and optionally also matching a serial
    /// number.
    pub fn scan(
        usb_vid_pid: Option<(u16, u16)>,
        usb_protocol: Option<(u8, u8, u8)>,
        usb_serial: Option<&str>,
    ) -> Result<Vec<(rusb::Device<rusb::Context>, String)>> {
        let mut devices = Vec::new();
        let mut deferred_log_messages = Vec::new();
        for device in rusb::Context::new()?.devices().context("USB error")?.iter() {
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

            if let Some((vid, pid)) = usb_vid_pid {
                if descriptor.vendor_id() != vid {
                    continue;
                }
                if descriptor.product_id() != pid {
                    continue;
                }
            }
            if let Some((class, subclass, protocol)) = usb_protocol {
                let config = match device.active_config_descriptor() {
                    Ok(desc) => desc,
                    Err(e) => {
                        deferred_log_messages.push(format!(
                            "Could not read config descriptor for device at bus={} address={}: {}",
                            device.bus_number(),
                            device.address(),
                            e,
                        ));
                        continue;
                    }
                };
                let mut found = false;
                for intf in config.interfaces() {
                    for desc in intf.descriptors() {
                        if desc.class_code() == class
                            && desc.sub_class_code() == subclass
                            && desc.protocol_code() == protocol
                        {
                            found = true;
                        }
                    }
                }
                if !found {
                    continue;
                }
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
            if let Some(sn) = &usb_serial
                && &serial_number != sn
            {
                continue;
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
        let mut devices = UsbBackend::scan(Some((usb_vid, usb_pid)), None, usb_serial)?;
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

    pub fn from_interface(
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
    ) -> Result<Self> {
        Self::from_interface_with_timeout(class, subclass, protocol, usb_serial, Duration::ZERO)
    }

    pub fn from_interface_with_timeout(
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Self> {
        let deadline = Instant::now() + timeout;
        loop {
            let mut devices =
                UsbBackend::scan(None, Some((class, subclass, protocol)), usb_serial)?;
            if devices.is_empty() {
                if Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(100));
                    continue;
                } else {
                    return Err(TransportError::NoDevice.into());
                }
            }
            ensure!(devices.len() == 1, TransportError::MultipleDevices);

            let (device, serial_number) = devices.remove(0);
            return Ok(UsbBackend {
                handle: device.open().context("USB open error")?,
                device,
                serial_number,
                timeout: Duration::from_millis(500),
            });
        }
    }

    pub fn handle(&self) -> &rusb::DeviceHandle<rusb::Context> {
        &self.handle
    }

    pub fn device(&self) -> &rusb::Device<rusb::Context> {
        &self.device
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

    pub fn set_active_configuration(&self, config: u8) -> Result<()> {
        self.handle
            .set_active_configuration(config)
            .context("USB error")
    }

    pub fn claim_interface(&self, iface: u8) -> Result<()> {
        self.handle.claim_interface(iface).context("USB error")
    }

    pub fn release_interface(&self, iface: u8) -> Result<()> {
        self.handle.release_interface(iface).context("USB error")
    }

    pub fn set_alternate_setting(&self, iface: u8, setting: u8) -> Result<()> {
        self.handle
            .set_alternate_setting(iface, setting)
            .context("USB error")
    }

    pub fn kernel_driver_active(&self, iface: u8) -> Result<bool> {
        self.handle.kernel_driver_active(iface).context("USB error")
    }

    pub fn detach_kernel_driver(&self, iface: u8) -> Result<()> {
        self.handle.detach_kernel_driver(iface).context("USB error")
    }

    pub fn attach_kernel_driver(&self, iface: u8) -> Result<()> {
        self.handle.attach_kernel_driver(iface).context("USB error")
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

    pub fn reset(&self) -> Result<()> {
        self.handle.reset().context("USB Error")
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

// Structure representing a USB hub. The device needs to have sufficient permission
// to be opened.
pub struct UsbHub {
    handle: rusb::DeviceHandle<rusb::Context>,
}

// USB hub operation.
pub enum UsbHubOp {
    // Power-off a specific port.
    PowerOff,
    // Power-on a specific port.
    PowerOn,
    // Suspend a specific port.
    Suspend,
    // Suspend a specific port.
    Resume,
    // Reset a specific port.
    Reset,
}

const PORT_SUSPEND: u16 = 2;
const PORT_RESET: u16 = 4;
const PORT_POWER: u16 = 8;

impl UsbHub {
    // Construct a hub from a device.
    pub fn from_device(dev: &rusb::Device<rusb::Context>) -> Result<UsbHub> {
        // Make sure the device is a hub.
        let dev_desc = dev.device_descriptor()?;
        // Assume that if the device has the HUB class then Linux will already enforce
        // that it follows the specification.
        ensure!(
            dev_desc.class_code() == rusb::constants::LIBUSB_CLASS_HUB,
            "device is not a hub"
        );
        Ok(UsbHub {
            handle: dev.open().context("cannot open hub")?,
        })
    }

    // Perform an operation.
    pub fn op(&self, op: UsbHubOp, port: u8, timeout: Duration) -> Result<()> {
        let (value, set_feature) = match op {
            UsbHubOp::Suspend => (PORT_SUSPEND, true),
            UsbHubOp::Resume => (PORT_SUSPEND, false),
            UsbHubOp::Reset => (PORT_RESET, true),
            UsbHubOp::PowerOn => (PORT_POWER, true),
            UsbHubOp::PowerOff => (PORT_POWER, false),
        };
        let req = if set_feature {
            rusb::constants::LIBUSB_REQUEST_SET_FEATURE
        } else {
            rusb::constants::LIBUSB_REQUEST_CLEAR_FEATURE
        };
        let req_type = rusb::constants::LIBUSB_RECIPIENT_OTHER
            | rusb::constants::LIBUSB_REQUEST_TYPE_CLASS
            | rusb::constants::LIBUSB_ENDPOINT_OUT;
        let _ = self
            .handle
            .write_control(req_type, req, value, port as u16, &[], timeout)?;
        Ok(())
    }
}
