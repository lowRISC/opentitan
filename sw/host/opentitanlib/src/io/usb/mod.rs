// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

pub mod desc;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use thiserror::Error;

use crate::impl_serializable_error;

/// Errors related to the GPIO interface.
#[derive(Debug, Error, Serialize, Deserialize)]
pub enum UsbError {
    #[error("Generic error: {0}")]
    Generic(String),
}
impl_serializable_error!(UsbError);

/// A trait which represents a USB device.
///
/// Note: some of the methods use `rusb`'s datatypes to avoid redefining
/// all USB structure but otherwise does not require rusb to be implemented.
pub trait UsbDevice {
    /// Return the VID of the device.
    fn get_vendor_id(&self) -> u16;

    /// Return the PID of the device.
    fn get_product_id(&self) -> u16;

    /// Gets the serial number of the device.
    fn get_serial_number(&self) -> &str;

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

    /// Return the currently active configuration's descriptor.
    fn active_configuration(&self) -> Result<desc::Configuration>;

    /// Return the device's bus number.
    fn bus_number(&self) -> u8;

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
}

/// A trait which represents a USB context.
pub trait UsbContext {
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
    fn device_by_id_with_timeout(
        &self,
        usb_vid: u16,
        usb_pid: u16,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Box<dyn UsbDevice>>;

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

    fn device_by_interface_with_timeout(
        &self,
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Box<dyn UsbDevice>>;
}
