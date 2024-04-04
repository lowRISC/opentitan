// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use clap::Parser;

use std::collections::HashSet;
use std::time::{Duration, Instant};

use opentitanlib::app::TransportWrapper;

#[derive(Debug, Parser)]
pub struct UsbOpts {
    /// USB vendor ID, default value is Google VID
    #[arg(long, value_parser = usb_id_parser, default_value = "18d1")]
    pub vid: u16,

    /// USB product ID, default value is lowRISC generic FS USB (allocated by Google).
    #[arg(long, value_parser = usb_id_parser, default_value = "503a")]
    pub pid: u16,

    /// Frequency at which to poll the USB bus for new device.
    #[arg(long, default_value = "10")]
    pub usb_poll_freq: u64,

    /// Pin to enable OT to sense VBUS.
    #[arg(long)]
    pub vbus_sense_en: Option<String>,

    /// Pin to sense VBUS.
    #[arg(long)]
    pub vbus_sense: Option<String>,
}

// Parse a USB VID/PID which must be a hex-string (e.g. "18d1").
fn usb_id_parser(id: &str) -> Result<u16> {
    Ok(u16::from_str_radix(id, 16)?)
}

// Represent an already seen device. Rely on the physical location (port numbers)
// instead of device address.
#[derive(Hash, PartialEq, Eq)]
struct DeviceLoc {
    bus: u8,
    port_numbers: Vec<u8>,
}

impl DeviceLoc {
    fn from_device(dev: &rusb::Device<rusb::GlobalContext>) -> Result<DeviceLoc> {
        Ok(DeviceLoc {
            bus: dev.bus_number(),
            port_numbers: dev.port_numbers()?,
        })
    }
}

impl UsbOpts {
    // Wait for a device that matches the USB VID/PID. If a device that matches
    // is found, it will try to open it: if that fails, a warning message will
    // logged (for debugging) and the function will continue waiting until a
    // a new device that can be opened is found. If several devices are found
    // at the time that match and can be open, all of them will be returned.
    // On timeout, the function will return an empty list.
    //
    // This function will return an error on critical failures such as failing to poll
    // the USB bus.
    pub fn wait_for_device(
        &self,
        timeout: Duration,
    ) -> Result<Vec<rusb::DeviceHandle<rusb::GlobalContext>>> {
        let start = Instant::now();
        // Keep a list of devices to not warn against again.
        let mut warned_desc = HashSet::<DeviceLoc>::new();
        let mut warned_open = HashSet::<DeviceLoc>::new();
        loop {
            let mut devices = Vec::new();
            for device in rusb::devices().context("USB error")?.iter() {
                let seen_dev = DeviceLoc::from_device(&device)?;
                let descriptor = match device.device_descriptor() {
                    Ok(desc) => desc,
                    Err(e) => {
                        // Ignore device if we have already seen it.
                        if !warned_desc.contains(&seen_dev) {
                            warned_desc.insert(seen_dev);
                            log::warn!("Could not read device descriptor for device at bus={} address={}: {}",
                                device.bus_number(),
                                device.address(),
                                e);
                        }
                        continue;
                    }
                };
                if descriptor.vendor_id() != self.vid {
                    continue;
                }
                if descriptor.product_id() != self.pid {
                    continue;
                }
                let handle = match device.open() {
                    Ok(handle) => handle,
                    Err(e) => {
                        // Ignore device if we have already seen it.
                        if !warned_open.contains(&seen_dev) {
                            warned_open.insert(seen_dev);
                            log::warn!(
                                "Could not open device at bus={} address={}: {}",
                                device.bus_number(),
                                device.address(),
                                e
                            );
                        }
                        continue;
                    }
                };
                devices.push(handle);
            }
            // Return if we found at least one device or if timeout has expired.
            if !devices.is_empty() || start.elapsed() >= timeout {
                return Ok(devices);
            }
            // Wait a bit before polling again.
            std::thread::sleep(Duration::from_micros(1_000_000u64 / self.usb_poll_freq));
        }
    }

    pub fn vbus_control_available(&self) -> bool {
        self.vbus_sense_en.is_some()
    }

    pub fn vbus_sense_available(&self) -> bool {
        self.vbus_sense.is_some()
    }

    // Enable/disable VBUS.
    pub fn enable_vbus(&self, transport: &TransportWrapper, en: bool) -> Result<()> {
        // Enable VBUS sense on the board if necessary.
        let Some(vbus_sense_en) = &self.vbus_sense_en else {
            bail!("cannot control VBUS, you must specify --vbus-sense-en");
        };
        log::info!("{} VBUS sensing.", if en { "Enable" } else { "Disable" });
        let vbus_sense_en_pin = transport.gpio_pin(vbus_sense_en)?;
        vbus_sense_en_pin.write(en)?;
        // Give time to hardware buffer to stabilize.
        std::thread::sleep(Duration::from_millis(100));
        Ok(())
    }

    // Check whether VBUS is present or not.
    pub fn vbus_present(&self, transport: &TransportWrapper) -> Result<bool> {
        // Sense VBUS if available.
        let Some(vbus_sense) = &self.vbus_sense else {
            bail!("cannot sense VBUS, you must specify --vbus-sense");
        };

        let vbus_sense_pin = transport.gpio_pin(vbus_sense)?;
        vbus_sense_pin.read()
    }
}

// Structure representing a USB hub. The device needs to have sufficient permission
// to be opened.
pub struct UsbHub {
    handle: rusb::DeviceHandle<rusb::GlobalContext>,
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
    pub fn from_device(dev: &rusb::Device<rusb::GlobalContext>) -> Result<UsbHub> {
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
