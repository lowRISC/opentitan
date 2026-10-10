// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod desc;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use thiserror::Error;

use crate::impl_serializable_error;
use crate::transport::TransportError;

/// Errors related to the GPIO interface.
#[derive(Debug, Error, Serialize, Deserialize)]
pub enum UsbError {
    #[error("Generic error: {0}")]
    Generic(String),
}
impl_serializable_error!(UsbError);

/// A trait which represents a USB device.
pub trait UsbDevice {
    /// Return the VID of the device.
    fn get_vendor_id(&self) -> u16;

    /// Return the PID of the device.
    fn get_product_id(&self) -> u16;

    /// Gets the serial number of the device.
    fn get_serial_number(&self) -> Option<&str>;

    /// Try to get the parent of this device (or None if root).
    fn get_parent(&self) -> Result<Box<dyn UsbDevice>>;

    /// Set the active configuration.
    fn set_active_configuration(&self, config: u8) -> Result<()>;

    /// Claim an interface for use with the kernel.
    fn claim_interface(&self, iface: u8) -> Result<()>;

    /// Release a previously claimed interface to the kernel.
    fn release_interface(&self, iface: u8) -> Result<()>;

    /// Set an interface alternate setting.
    fn set_alternate_setting(&self, iface: u8, setting: u8) -> Result<()>;

    /// Check whether a kernel driver currentl controls the device.
    fn kernel_driver_active(&self, iface: u8) -> Result<bool>;

    /// Detach the kernel driver from the device.
    fn detach_kernel_driver(&self, iface: u8) -> Result<()>;

    /// Attach the kernel driver to the device.
    fn attach_kernel_driver(&self, iface: u8) -> Result<()>;

    /// Return the device's descriptor.
    fn device_descriptor(&self) -> desc::Device<'_>;

    /// Return the currently active configuration's descriptor.
    fn active_configuration(&self) -> Result<desc::Configuration<'_>>;

    /// Return the device's bus number.
    fn bus_number(&self) -> u8;

    /// Return the device's address.
    fn address(&self) -> u8;

    /// Return the sequence of port numbers from the root down to the device.
    fn port_numbers(&self) -> Result<Vec<u8>>;

    /// Return a string descriptor in ASCII.
    fn read_string_descriptor_ascii(&self, idx: u8) -> Result<String>;

    /// Reset the device.
    ///
    /// Note that this UsbDevice handle will most likely become invalid
    /// after resetting the device and a new one has to be obtained.
    fn reset(&self) -> Result<()>;

    /// Get the default timeout for operations.
    fn get_timeout(&self) -> Duration;

    /// Issue a USB control request with optional host-to-device data.
    fn write_control_timeout(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &[u8],
        timeout: Duration,
    ) -> Result<usize>;

    /// Issue a USB control request with optional host-to-device data.
    ///
    /// This function uses the default timeout set up by the context.
    fn write_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &[u8],
    ) -> Result<usize> {
        self.write_control_timeout(request_type, request, value, index, buf, self.get_timeout())
    }

    /// Issue a USB control request with optional device-to-host data.
    fn read_control_timeout(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &mut [u8],
        timeout: Duration,
    ) -> Result<usize>;

    /// Issue a USB control request with optional device-to-host data.
    ///
    /// This function uses the default timeout set up by the context.
    fn read_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &mut [u8],
    ) -> Result<usize> {
        self.read_control_timeout(request_type, request, value, index, buf, self.get_timeout())
    }

    /// Read bulk data bytes to given USB endpoint.
    fn read_bulk_timeout(&self, endpoint: u8, data: &mut [u8], timeout: Duration) -> Result<usize>;

    /// Read bulk data bytes to given USB endpoint.
    ///
    /// This function uses the default timeout set up by the context.
    fn read_bulk(&self, endpoint: u8, data: &mut [u8]) -> Result<usize> {
        self.read_bulk_timeout(endpoint, data, self.get_timeout())
    }

    /// Write bulk data bytes to given USB endpoint.
    fn write_bulk_timeout(&self, endpoint: u8, data: &[u8], timeout: Duration) -> Result<usize>;

    /// Write bulk data bytes to given USB endpoint.
    ///
    /// This function uses the default timeout set up by the context.
    fn write_bulk(&self, endpoint: u8, data: &[u8]) -> Result<usize> {
        self.write_bulk_timeout(endpoint, data, self.get_timeout())
    }

    /// Test whether two instances refer to the same underlying USB device.
    fn eq(&self, other: &dyn UsbDevice) -> bool {
        self.bus_number() == other.bus_number() && self.address() == other.address()
    }
}

impl std::fmt::Debug for dyn UsbDevice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(
            f,
            "{}-{} [vid={:x},pid={:x},address={},serial={}]",
            self.bus_number(),
            self.port_numbers()
                .map(|ports| ports
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("."))
                .unwrap_or("<ports unavailable>".into()),
            self.get_vendor_id(),
            self.get_product_id(),
            self.address(),
            self.get_serial_number().unwrap_or("<not available>"),
        )
    }
}

/// Defaut poll interval for timeout-based functions in the USB context.
const DEVICE_POLL_INTERVAL_MILLIS: u64 = 100;

fn look_for_device<T: UsbContext + ?Sized>(
    ctx: &T,
    usb_vid: Option<u16>,
    usb_pid: Option<u16>,
    usb_protocol: Option<(u8, u8, u8)>,
    usb_serial: Option<&str>,
    timeout: Duration,
    search_criterion: &str,
) -> Result<Box<dyn UsbDevice>> {
    let deadline = Instant::now() + timeout;
    let search_criterion = if let Some(s) = usb_serial {
        format!("{} (serial={})", search_criterion, s)
    } else {
        search_criterion.to_string()
    };
    loop {
        let mut devices = ctx.scan(usb_vid, usb_pid, usb_protocol, usb_serial)?;
        if devices.is_empty() {
            if Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(DEVICE_POLL_INTERVAL_MILLIS));
                continue;
            } else {
                return Err(TransportError::NoDevice(search_criterion).into());
            }
        }
        if devices.len() > 1 {
            return Err(TransportError::MultipleDevices(
                format!("{:?}", devices),
                search_criterion,
            )
            .into());
        }

        return Ok(devices.remove(0));
    }
}

/// A trait which represents a USB context.
pub trait UsbContext {
    /// Scan the USB bus for devices matching VID/PID, and optionally also matching a serial
    /// number. This method always returns immediately with the list of currently plugged
    /// devices matching the requested criteria.
    fn scan(
        &self,
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_protocol: Option<(u8, u8, u8)>,
        usb_serial: Option<&str>,
    ) -> Result<Vec<Box<dyn UsbDevice>>>;

    /// Find a device by VID:PID, and optionally disambiguate by serial number.
    ///
    /// If no device matches, this function returns immediately and does not wait.
    fn device_by_id(
        &self,
        usb_vid: u16,
        usb_pid: u16,
        usb_serial: Option<&str>,
    ) -> Result<Box<dyn UsbDevice>> {
        self.device_by_id_with_timeout(usb_vid, usb_pid, usb_serial, Duration::ZERO)
    }

    /// Find a device by VID:PID, and optionally disambiguate by serial number.
    ///
    /// If no device matches, this function will keep trying until the provided timeout expires.
    fn device_by_id_with_timeout(
        &self,
        usb_vid: u16,
        usb_pid: u16,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Box<dyn UsbDevice>> {
        look_for_device(
            self,
            Some(usb_vid),
            Some(usb_pid),
            None,
            usb_serial,
            timeout,
            &format!("vid:pid=0x{:04x}:0x{:04x}", usb_vid, usb_pid),
        )
    }

    /// Find a device with a specific interface, and optionally disambiguate by serial number.
    ///
    /// If no device matches, this function returns immediately and does not wait.
    fn device_by_interface(
        &self,
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
    ) -> Result<Box<dyn UsbDevice>> {
        self.device_by_interface_with_timeout(class, subclass, protocol, usb_serial, Duration::ZERO)
    }

    /// Find a device with a specific interface, and optionally disambiguate by serial number.
    ///
    /// If no device matches, this function will keep trying until the provided timeout expires.
    fn device_by_interface_with_timeout(
        &self,
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Box<dyn UsbDevice>> {
        look_for_device(
            self,
            None,
            None,
            Some((class, subclass, protocol)),
            usb_serial,
            timeout,
            &format!(
                "class:subclass:protocol=0x{:02x}:0x{:02x}:0x{:02x}",
                class, subclass, protocol
            ),
        )
    }
}
