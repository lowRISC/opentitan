// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This utility handles the discovery of TTY device. It does not use serialport
// at the moment because this code needs to work in non-udev environment and
// make as little assumptions are possible. This code also works for USB devices.
use std::fs;
use std::path::Path;

use anyhow::{Context, Result};
use regex::Regex;

/// A discovered USB TTY.
#[derive(Debug, Clone)]
pub struct UsbTty {
    pub port_name: String,             // Name of the port, e.g. ttyACM0.
    pub vid: u16,                      // USB vendor ID.
    pub pid: u16,                      // USB vendor ID.
    pub serial_number: Option<String>, // USB serial number (if any).
    pub interface: u8,                 // USB Interface number.
    pub config: u8,                    // USB configuration number.
    pub bus: u8,                       // USB bus number.
    pub ports: Vec<u8>,                // USB port numbers.
}

/// Path to the linux sysfs USB device tree.
pub const SYSFS_USB_PATH: &str = "/sys/bus/usb/devices";

pub fn scan_usb_ttys() -> Result<Vec<UsbTty>> {
    // The devices directory looks something like this (see https://www.kernel.org/doc/Documentation/ABI/stable/sysfs-bus-usb):
    //
    // ```plain
    // 3-6/         # USB device
    // |- 3-6:1.0/  # USB Interface
    // |- 3-6:1.1/  # USB Interface
    // |- 3-6:1.2/  # USB Interface
    // |- 3-6:1.3/  # USB Interface
    // |- 3-6:1.3/  # USB Interface
    // |- power/    # Other device stuff...
    // |- idVendor  # USB vendor ID
    // |- idProduct # USB product ID
    // |- ...
    //
    // 4-2/         # USB device
    // |- 4-2:1.0/  # USB Interface
    // |- ...
    // ...
    // ```
    //
    // Note that devices under several hubs have a more complex path like 3-1.4.3 which is more generally
    // of the form <bus>-<port1>[.<portX>]*
    // And the interface are numbered as <config>.<interface>
    let mut list = Vec::new();

    // Regex for a full usb path: <bus>-<port1>[.<portX>]*:<cfg>.<intf>
    let usb_re = Regex::new(
        r"^(?<bus>[0-9]+)-(?<ports>[0-9]+(?:\.[0-9]+)*):(?<cfg>[0-9]+)\.(?<intf>[0-9]+)$",
    )
    .context("Could not build regex to match interfaces")?;

    for dev in fs::read_dir(SYSFS_USB_PATH).context("Cannot find USB device in sysfs")? {
        let dirent = dev?;
        let dev_path = dirent.path();
        let dev_name = dirent
            .file_name()
            .to_str()
            .context("Cannot convert filename to string")?
            .to_string();
        // Only consider devices.
        if !dev_path.is_dir() || dev_name.contains(':') {
            continue;
        }
        // Read VID, PID and serial.
        let vid = u16::from_str_radix(fs::read_to_string(dev_path.join("idVendor"))?.trim(), 16)?;
        let pid = u16::from_str_radix(fs::read_to_string(dev_path.join("idProduct"))?.trim(), 16)?;
        let serial_number_path = dev_path.join("serial");
        let serial_number = if serial_number_path.exists() {
            Some(fs::read_to_string(serial_number_path)?.trim().to_string())
        } else {
            None
        };

        // List interfaces.
        for iface in dev_path.read_dir()? {
            let iface_dirent = iface?;
            let iface_name = iface_dirent
                .file_name()
                .to_str()
                .context("sysfs filename is not in UTF9")?
                .to_string();
            let captures = match usb_re.captures(&iface_name) {
                None => {
                    // Not an interface directory.
                    continue;
                }
                Some(captures) => captures,
            };
            let bus = captures["bus"].parse::<u8>()?;
            let ports = captures["ports"]
                .split('.')
                .map(|x| x.parse::<u8>().context("sysfs usb ports is invalid"))
                .collect::<Result<Vec<_>>>()?;
            let config = captures["cfg"].parse::<u8>()?;
            let interface = captures["intf"].parse::<u8>()?;
            // Look for a TTY in this directory.
            let port_name = match find_tty_in_usb_dir(&iface_dirent.path())? {
                None => continue,
                Some(port_name) => port_name,
            };

            list.push(UsbTty {
                port_name: format!("/dev/{}", port_name),
                vid,
                pid,
                serial_number: serial_number.clone(),
                interface,
                config,
                bus,
                ports,
            })
        }
    }

    Ok(list)
}

fn find_the_tty(path: &Path) -> Result<Option<String>> {
    // Expect a single device under tty/ so return the first entry.
    let child = path
        .read_dir()
        .context("Cannot list tty directory in sysfs")?
        .next()
        .context("The tty directory in sysfs is empty!")?;
    let filename = child?.file_name();
    Ok(Some(filename.to_str().context("bad")?.to_string()))
}

fn find_tty_in_usb_dir(path: &Path) -> Result<Option<String>> {
    // There seems to be an inconsistency in the naming of tty directories
    // under USB interface: cdcacn creates a device `tty/ttyACMx` but ftdi_sio
    // creates `ttyUSBx/tty/ttyUSBx`.

    let the_tty = path.join("tty");
    if the_tty.exists() {
        return find_the_tty(&the_tty);
    }

    for child in path.read_dir()? {
        let child_path = child?.path();
        let the_tty = child_path.join("tty");
        if the_tty.exists() {
            return find_the_tty(&the_tty);
        }
    }
    Ok(None)
}
