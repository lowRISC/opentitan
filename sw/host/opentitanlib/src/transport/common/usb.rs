// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result, ensure};
use rusb::{self, UsbContext};
use std::time::{Duration, Instant};

use crate::io::usb::{UsbContext as OtUsbContext, UsbDevice, desc};
use crate::transport::TransportError;

/// Represents a device provided by the `rusb` crate.
pub struct RusbDevice {
    handle: rusb::DeviceHandle<rusb::Context>,
    serial_number: Option<String>,
    timeout: Duration,
    device_desc: Vec<u8>,
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
        let serial_str = if let Some(s) = usb_serial {
            format!(" (serial={})", s)
        } else {
            String::new()
        };
        loop {
            let mut devices = RusbContext::scan(Some((usb_vid, usb_pid)), None, usb_serial)?;
            if devices.is_empty() {
                if Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(100));
                    continue;
                } else {
                    return Err(TransportError::NoDevice(format!(
                        "vid:pid=0x{:04x}:0x{:04x}{}",
                        usb_vid, usb_pid, serial_str
                    ))
                    .into());
                }
            }
            if devices.len() > 1 {
                return Err(TransportError::MultipleDevices(
                    format!("{:?}", devices),
                    format!("vid:pid=0x{:04x}:0x{:04x}{}", usb_vid, usb_pid, serial_str),
                )
                .into());
            }

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
        let serial_str = if let Some(s) = usb_serial {
            format!(" (serial={})", s)
        } else {
            String::new()
        };
        loop {
            let mut devices =
                RusbContext::scan(None, Some((class, subclass, protocol)), usb_serial)?;
            if devices.is_empty() {
                if Instant::now() < deadline {
                    std::thread::sleep(Duration::from_millis(100));
                    continue;
                } else {
                    return Err(TransportError::NoDevice(format!(
                        "class:subclass:protocol=0x{:02x}:0x{:02x}:0x{:02x}{}",
                        class, subclass, protocol, serial_str
                    ))
                    .into());
                }
            }
            if devices.len() > 1 {
                return Err(TransportError::MultipleDevices(
                    format!("{:?}", devices),
                    format!(
                        "class:subclass:protocol=0x{:02x}:0x{:02x}:0x{:02x}{}",
                        class, subclass, protocol, serial_str
                    ),
                )
                .into());
            }

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
    pub fn new(
        handle: rusb::DeviceHandle<rusb::Context>,
        serial_number: Option<String>,
        timeout: Duration,
    ) -> Result<Self> {
        let mut configurations = Vec::new();

        // Unfortunately, rusb simply wraps around libusb which does not
        // give access to the raw configuration descriptor so we must
        // get it directly from the device.
        let dev_desc_size = handle.device().device_descriptor()?.length() as usize;
        let mut device_desc = vec![0u8; dev_desc_size];
        let size = handle
            .read_control(
                0x80,   // Standard, device, IN
                6,      // GET_DESCRIPTOR
                1 << 8, // DEVICE
                0,
                &mut device_desc,
                timeout,
            )
            .context("could not retrieve device descriptor")?;
        ensure!(
            size == dev_desc_size,
            "Device did not return the full device descriptor"
        );

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
            device_desc,
            configurations,
        })
    }
}

impl UsbDevice for RusbDevice {
    fn get_timeout(&self) -> Duration {
        self.timeout
    }

    fn get_parent(&self) -> Result<Box<dyn UsbDevice>> {
        let device = self
            .handle
            .device()
            .get_parent()
            .context("Unable to get parent USB device")?;
        let handle = device.open().context(format!(
            "Could not open device at bus={} address={}",
            device.bus_number(),
            device.address(),
        ))?;
        // We do not try to read the serial number of the parent because hubs generally do not have
        // unique serial numbers.
        Ok(Box::new(RusbDevice::new(handle, None, self.get_timeout())?))
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

    fn device_descriptor(&self) -> desc::Device<'_> {
        desc::Device::new(&self.device_desc)
    }

    fn active_configuration(&self) -> Result<desc::Configuration<'_>> {
        let active_cfg_val = self
            .handle
            .active_configuration()
            .context("Cannot retrieve active configuration value")?;
        // Find the configuration matching the currently active one.
        for cfg in self.configurations.iter() {
            let cfg = desc::Configuration::new(cfg);
            if let Ok(desc) = cfg.descriptor()
                && desc.config_val == active_cfg_val
            {
                return Ok(cfg);
            }
        }
        anyhow::bail!("No configuration corresponds to the configuration value {active_cfg_val:?}")
    }

    fn bus_number(&self) -> u8 {
        self.handle.device().bus_number()
    }

    fn address(&self) -> u8 {
        self.handle.device().address()
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
    handle: Box<dyn UsbDevice>,
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
    // Construct a hub from the parent of a device.
    pub fn from_parent_device(dev: &dyn UsbDevice) -> Result<UsbHub> {
        let handle = dev.get_parent().with_context(|| {
            format!(
                "Cannot access USB parent hub of device on bus {bus}, address {addr}\n\
                If this test requires access to the HUB, you need to make sure that \
                the program has sufficient permissions to access the hub\n\
                See sw/host/tests/chip/usb/README.md for more information\n\
                The following command may fix the issue:\n\
                sudo chmod 0666 /dev/bus/usb/{bus:03}/ADDR\n\
                where ADDR is the address of the hub",
                bus = dev.bus_number(),
                addr = dev.address(),
            )
        })?;
        UsbHub::from_device(handle)
    }

    // Construct a hub from a device.
    pub fn from_device(dev: Box<dyn UsbDevice>) -> Result<UsbHub> {
        // Make sure the device is a hub.
        let dev_desc = dev.device_descriptor().descriptor()?;
        // Assume that if the device has the HUB class then Linux will already enforce
        // that it follows the specification.
        ensure!(
            dev_desc.class == rusb::constants::LIBUSB_CLASS_HUB,
            "device is not a hub"
        );
        Ok(UsbHub { handle: dev })
    }

    pub fn device(&self) -> &dyn UsbDevice {
        &*self.handle
    }

    // Report the status of a port (only returns the port status, not the port change).
    fn port_status(&self, port: u8, timeout: Duration) -> Result<u16> {
        let req_type = rusb::constants::LIBUSB_RECIPIENT_OTHER
            | rusb::constants::LIBUSB_REQUEST_TYPE_CLASS
            | rusb::constants::LIBUSB_ENDPOINT_IN;
        let mut status = [0u8; 4];
        let _ = self.handle.read_control_timeout(
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
            UsbHubOp::PowerOn => (PORT_POWER, true, "power on"),
            UsbHubOp::PowerOff => (PORT_POWER, false, "power off"),
        };
        let req = if set_feature {
            rusb::constants::LIBUSB_REQUEST_SET_FEATURE
        } else {
            rusb::constants::LIBUSB_REQUEST_CLEAR_FEATURE
        };
        let req_type = rusb::constants::LIBUSB_RECIPIENT_OTHER
            | rusb::constants::LIBUSB_REQUEST_TYPE_CLASS
            | rusb::constants::LIBUSB_ENDPOINT_OUT;
        // Expected port status after the operation.
        let port_status_mask = 1u16 << feature_index;
        let port_status_after = if set_feature { port_status_mask } else { 0u16 };

        // Perform operation.
        let _ = self.handle.write_control_timeout(
            req_type,
            req,
            feature_index,
            port as u16,
            &[],
            timeout,
        )?;
        // Wait until port has changed status.
        if !check_status {
            return Ok(());
        }
        let start = Instant::now();
        loop {
            let port_status = self.port_status(port, timeout)?;
            if port_status & port_status_mask == port_status_after {
                break;
            }
            if start.elapsed() >= timeout {
                anyhow::bail!(
                    "Trying to {} port {} but port did not change status (last status was {:x})",
                    human_op,
                    port,
                    port_status
                );
            }
        }
        log::info!("{} performed in {:#?}", human_op, start.elapsed());

        Ok(())
    }
}
