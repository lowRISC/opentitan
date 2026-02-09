// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result, bail, ensure};
use rusb::{self, UsbContext};
use std::time::{Duration, Instant};

use crate::io::usb::{UsbContext as OtUsbContext, UsbDevice, desc::Configuration};
use crate::transport::TransportError;

/// Represents a device provided by the `rusb` crate.
pub struct RusbDevice {
    handle: rusb::DeviceHandle<rusb::Context>,
    serial_number: Option<String>,
    timeout: Duration,
    configurations: Vec<Vec<u8>>,
}

/// Represents a backend using the `rusb` crate.
#[derive(Default)]
pub struct RusbContext {}

impl RusbContext {
    pub fn new() -> Self {
        RusbContext::default()
    }

    /// Scan the USB bus for a device matching VID/PID, and optionally also matching a serial
    /// number.
    fn scan(
        usb_vid_pid: Option<(u16, u16)>,
        usb_protocol: Option<(u8, u8, u8)>,
        usb_serial: Option<&str>,
    ) -> Result<Vec<(rusb::Device<rusb::Context>, Option<String>)>> {
        let mut devices = Vec::new();
        let mut deferred_log_messages = Vec::new();
        // The global context sometimes fails to detect new devices which causes some
        // really puzzling errors. Here we create a new context for every scan.
        // Although less efficient, this works around most of the issues with hotplug.
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

            let serial_number = if descriptor.serial_number_string_index().is_some() {
                match handle.read_serial_number_string_ascii(&descriptor) {
                    Ok(sn) => Some(sn),
                    Err(e) => {
                        deferred_log_messages.push(format!(
                            "Could not read serial number from device at bus={} address={}: {}",
                            device.bus_number(),
                            device.address(),
                            e,
                        ));
                        continue;
                    }
                }
            } else {
                None
            };
            if usb_serial.is_some() && serial_number.as_deref() != usb_serial {
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
}

impl OtUsbContext for RusbContext {
    fn device_by_id_with_timeout(
        &self,
        usb_vid: u16,
        usb_pid: u16,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Box<dyn UsbDevice>> {
        let deadline = Instant::now() + timeout;
        loop {
            let mut devices = RusbContext::scan(Some((usb_vid, usb_pid)), None, usb_serial)?;
            if devices.is_empty() {
                if Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(100));
                    continue;
                } else {
                    return Err(TransportError::NoDevice.into());
                }
            }
            ensure!(
                devices.len() == 1,
                TransportError::MultipleDevices(format!("{:?}", devices))
            );

            let (device, serial_number) = devices.remove(0);
            return Ok(Box::new(RusbDevice::new(
                device
                    .open()
                    .with_context(|| format!("Cannot open device {device:?}"))?,
                serial_number,
                Duration::from_millis(500),
            )?));
        }
    }

    fn device_by_interface_with_timeout(
        &self,
        class: u8,
        subclass: u8,
        protocol: u8,
        usb_serial: Option<&str>,
        timeout: Duration,
    ) -> Result<Box<dyn UsbDevice>> {
        let deadline = Instant::now() + timeout;
        loop {
            let mut devices =
                RusbContext::scan(None, Some((class, subclass, protocol)), usb_serial)?;
            if devices.is_empty() {
                if Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(100));
                    continue;
                } else {
                    return Err(TransportError::NoDevice.into());
                }
            }
            ensure!(
                devices.len() == 1,
                TransportError::MultipleDevices(format!("{:?}", devices))
            );

            let (device, serial_number) = devices.remove(0);
            return Ok(Box::new(RusbDevice::new(
                device
                    .open()
                    .with_context(|| format!("Cannot open device {device:?}"))?,
                serial_number,
                Duration::from_millis(500),
            )?));
        }
    }
}

impl RusbDevice {
    fn new(
        handle: rusb::DeviceHandle<rusb::Context>,
        serial_number: Option<String>,
        timeout: Duration,
    ) -> Result<Self> {
        let mut configurations = Vec::new();

        // Unfortunately, rusb simply wraps around libusb which does not
        // give access to the raw configuration descriptor so we must
        // get it directly from the device.
        let nr_config = handle
            .device()
            .device_descriptor()
            .context("could not retrieve device descriptor")?
            .num_configurations();
        for config_idx in 0..nr_config {
            let tot_len = handle
                .device()
                .config_descriptor(config_idx)
                .context("could not retrieve config descriptor")?
                .total_length() as usize;
            let mut desc = vec![0u8; tot_len];
            let size = handle
                .read_control(
                    0x80,                       // Standard, device, IN
                    6,                          // GET_DESCRIPTOR
                    2 << 8 | config_idx as u16, // CONFIGURATION
                    0,
                    &mut desc,
                    timeout,
                )
                .context("could not retrieve config descriptor")?;
            ensure!(
                size == tot_len,
                "Device did not return the full configuration descriptor"
            );
            configurations.push(desc)
        }

        Ok(RusbDevice {
            handle,
            serial_number,
            timeout,
            configurations,
        })
    }
}

impl UsbDevice for RusbDevice {
    fn get_timeout(&self) -> Duration {
        self.timeout
    }

    fn get_vendor_id(&self) -> u16 {
        self.handle
            .device()
            .device_descriptor()
            .unwrap()
            .vendor_id()
    }

    fn get_product_id(&self) -> u16 {
        self.handle
            .device()
            .device_descriptor()
            .unwrap()
            .product_id()
    }

    /// Gets the usb serial number of the device.
    fn get_serial_number(&self) -> Option<&str> {
        self.serial_number.as_deref()
    }

    fn set_active_configuration(&self, config: u8) -> Result<()> {
        self.handle
            .set_active_configuration(config)
            .context("USB error")
    }

    fn claim_interface(&self, iface: u8) -> Result<()> {
        self.handle.claim_interface(iface).context("USB error")
    }

    fn release_interface(&self, iface: u8) -> Result<()> {
        self.handle.release_interface(iface).context("USB error")
    }

    fn set_alternate_setting(&self, iface: u8, setting: u8) -> Result<()> {
        self.handle
            .set_alternate_setting(iface, setting)
            .context("USB error")
    }

    fn kernel_driver_active(&self, iface: u8) -> Result<bool> {
        self.handle.kernel_driver_active(iface).context("USB error")
    }

    fn detach_kernel_driver(&self, iface: u8) -> Result<()> {
        self.handle.detach_kernel_driver(iface).context("USB error")
    }

    fn attach_kernel_driver(&self, iface: u8) -> Result<()> {
        self.handle.attach_kernel_driver(iface).context("USB error")
    }

    fn active_configuration(&self) -> Result<Configuration> {
        let active_cfg_val = self
            .handle
            .active_configuration()
            .context("Cannot retrieve active configuration value")?;
        // Find the configuration matching the currently active one.
        for cfg in self.configurations.iter() {
            let cfg = Configuration::new(cfg);
            if let Ok(desc) = cfg.descriptor() {
                if desc.config_val == active_cfg_val {
                    return Ok(cfg);
                }
            }
        }
        anyhow::bail!("No configuration corresponds to the configuration value {active_cfg_val:?}")
    }

    fn bus_number(&self) -> u8 {
        self.handle.device().bus_number()
    }

    fn port_numbers(&self) -> Result<Vec<u8>> {
        self.handle.device().port_numbers().context("USB error")
    }

    fn read_string_descriptor_ascii(&self, idx: u8) -> Result<String> {
        self.handle
            .read_string_descriptor_ascii(idx)
            .context("USB error")
    }

    fn reset(&self) -> Result<()> {
        self.handle.reset().context("USB Error")
    }

    fn write_control_timeout(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &[u8],
        timeout: Duration,
    ) -> Result<usize> {
        self.handle
            .write_control(request_type, request, value, index, buf, timeout)
            .context("USB error")
    }

    fn read_control_timeout(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        buf: &mut [u8],
        timeout: Duration,
    ) -> Result<usize> {
        self.handle
            .read_control(request_type, request, value, index, buf, timeout)
            .context("USB error")
    }

    fn read_bulk_timeout(&self, endpoint: u8, data: &mut [u8], timeout: Duration) -> Result<usize> {
        let len = self
            .handle
            .read_bulk(endpoint, data, timeout)
            .context("USB error")?;
        Ok(len)
    }

    fn write_bulk_timeout(&self, endpoint: u8, data: &[u8], timeout: Duration) -> Result<usize> {
        let len = self
            .handle
            .write_bulk(endpoint, data, timeout)
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
    // Suspend a specific port.
    Suspend,
    // Suspend a specific port.
    Resume,
    // Reset a specific port.
    Reset,
}

const PORT_SUSPEND: u16 = 2;
const PORT_RESET: u16 = 4;

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
            handle: dev.open().with_context(|| {
                format!(
                    "Cannot access USB hub on bus {bus}, address {addr}\n\
                If this test requires access to the HUB, you need to make sure that \
                the program has sufficient permissions to access the hub\n\
                See sw/host/tests/chip/usb/README.md for more information\n\
                The following command may fix the issue:\n\
                sudo chmod 0666 /dev/bus/usb/{bus:03}/{addr:03}",
                    bus = dev.bus_number(),
                    addr = dev.address(),
                )
            })?,
        })
    }

    pub fn device(&self) -> rusb::Device<rusb::Context> {
        self.handle.device()
    }

    // Report the status of a port (only returns the port status, not the port change).
    fn port_status(&self, port: u8, timeout: Duration) -> Result<u16> {
        let req_type = rusb::constants::LIBUSB_RECIPIENT_OTHER
            | rusb::constants::LIBUSB_REQUEST_TYPE_CLASS
            | rusb::constants::LIBUSB_ENDPOINT_IN;
        let mut status = [0u8; 4];
        let _ = self.handle.read_control(
            req_type,
            rusb::constants::LIBUSB_REQUEST_GET_STATUS,
            0,
            port as u16,
            &mut status,
            timeout,
        )?;
        Ok(status[0] as u16 | (status[1] as u16) << 8)
    }

    // Perform an operation.
    pub fn op(&self, op: UsbHubOp, port: u8, timeout: Duration, check_status: bool) -> Result<()> {
        let (feature_index, set_feature, human_op) = match op {
            UsbHubOp::Suspend => (PORT_SUSPEND, true, "suspend"),
            UsbHubOp::Resume => (PORT_SUSPEND, false, "resume"),
            UsbHubOp::Reset => (PORT_RESET, true, "reset"),
        };
        let req = if set_feature {
            rusb::constants::LIBUSB_REQUEST_SET_FEATURE
        } else {
            rusb::constants::LIBUSB_REQUEST_CLEAR_FEATURE
        };
        let req_type = rusb::constants::LIBUSB_RECIPIENT_OTHER
            | rusb::constants::LIBUSB_REQUEST_TYPE_CLASS
            | rusb::constants::LIBUSB_ENDPOINT_OUT;
        // Make sure that the port status is the expected one before the operation.
        let port_status_mask = 1u16 << feature_index;
        let port_status_before = if set_feature { 0u16 } else { port_status_mask };
        let port_status_after = if set_feature { port_status_mask } else { 0u16 };

        if check_status {
            let port_status = self.port_status(port, timeout)?;
            ensure!(
                port_status & port_status_mask == port_status_before,
                "Trying to {} port {} but port has unexpected status {:#x}",
                human_op,
                port,
                port_status
            );
        }
        // Perform operation.
        let _ =
            self.handle
                .write_control(req_type, req, feature_index, port as u16, &[], timeout)?;
        // Wait until port has changed status.
        if check_status {
            let start = Instant::now();
            loop {
                let port_status = self.port_status(port, timeout)?;
                if port_status & port_status_mask == port_status_after {
                    break;
                }
                if start.elapsed() >= timeout {
                    bail!(
                        "Trying to {} port {} but port did not change status (last status was {:x})",
                        human_op,
                        port,
                        port_status
                    );
                }
            }
            log::info!("{} performed in {:#?}", human_op, start.elapsed());
        }

        Ok(())
    }
}
