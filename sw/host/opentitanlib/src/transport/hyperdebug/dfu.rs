// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Firmware update protocol for HyperDebug

use anyhow::{anyhow, bail, Context, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::cell::RefCell;

use crate::transport::{
    Capabilities, Capability, ProgressIndicator, Transport, TransportError, UpdateFirmware,
};
use crate::util::usb::UsbBackend;

const VID_ST_MICROELECTRONICS: u16 = 0x0483;
const PID_DFU_BOOTLOADER: u16 = 0xdf11;

/// This transport is to be used if a Nucleo board is already in DFU bootloader mode at the time
/// of the `opentitantool` invocation (and presenting itself with STMs VID:DID, rather than
/// Google's).
pub struct HyperdebugDfu {
    usb_backend: RefCell<UsbBackend>,
    current_firmware_version: Option<String>,
}

impl HyperdebugDfu {
    /// Establish connection with a particular Nucleo-L552ZE board possibly already in DFU
    /// bootloader mode.
    pub fn open(
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: Option<&str>,
    ) -> Result<Self> {
        // Look for a device with given USB serial, carrying either the VID:DID of STM32 DFU
        // bootloader, or that of HyperDebug in ordinary mode.  This allows scripts to start with
        // `opentitantool --interface hyperdebug_dfu transport update-firmware`, knowing that it
        // will put the desired firmware on the HyperDebug, both in the case of previous
        // interrupted update, as well as the ordinary case of outdated or current HyperDebug
        // firmware already running.
        if let Ok(usb_backend) = UsbBackend::new(
            usb_vid.unwrap_or(VID_ST_MICROELECTRONICS),
            usb_pid.unwrap_or(PID_DFU_BOOTLOADER),
            usb_serial,
        ) {
            // HyperDebug device is already in DFU mode, we cannot query firmware version through
            // USB strings.  (And the fact that it was left in DFU mode, probably as a result of a
            // previous incomplete update attempt, should mean that we would not want to trust the
            // version, even if we could extract it through the DFU firmware.)
            return Ok(Self {
                usb_backend: RefCell::new(usb_backend),
                current_firmware_version: None,
            });
        }

        let usb_backend = UsbBackend::new(
            usb_vid.unwrap_or(super::VID_GOOGLE),
            usb_pid.unwrap_or(super::PID_HYPERDEBUG),
            usb_serial,
        )?;
        // HyperDebug device in operational mode, look at the USB strings for the running firmware
        // version.
        let config_desc = usb_backend.active_config_descriptor()?;
        let current_firmware_version = if let Some(idx) = config_desc.description_string_index() {
            if let Ok(current_firmware_version) = usb_backend.read_string_descriptor_ascii(idx) {
                Some(current_firmware_version)
            } else {
                None
            }
        } else {
            None
        };
        Ok(Self {
            usb_backend: RefCell::new(usb_backend),
            current_firmware_version,
        })
    }
}

/// The device does not support any part of the Transport trait, except the UpdateFirmware action.
impl Transport for HyperdebugDfu {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(Capability::NONE))
    }

    fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Annotate>>> {
        if let Some(update_firmware_action) = action.downcast_ref::<UpdateFirmware>() {
            update_firmware(
                &mut self.usb_backend.borrow_mut(),
                self.current_firmware_version.as_deref(),
                &update_firmware_action.firmware,
                update_firmware_action.progress.as_ref(),
                update_firmware_action.force,
            )
        } else {
            bail!(TransportError::UnsupportedOperation)
        }
    }
}

const USB_CLASS_APP: u8 = 0xFE;
const USB_SUBCLASS_DFU: u8 = 0x01;

const DFUSE_ERASE_PAGE: u8 = 0x41;
const DFUSE_PROGRAM_PAGE: u8 = 0x21;

const DFU_STATUS_OK: u8 = 0x00;

const DFU_STATE_APP_IDLE: u8 = 0x00;
const DFU_STATE_DFU_IDLE: u8 = 0x02;
const DFU_STATE_DOWNLOAD_BUSY: u8 = 0x04;
const DFU_STATE_DOWNLOAD_IDLE: u8 = 0x05;

const USB_DFU_DETACH: u8 = 0;
const USB_DFU_DNLOAD: u8 = 1;
const USB_DFU_GETSTATUS: u8 = 3;

#[cfg(not(feature = "include_hyperdebug_firmware"))]
const OFFICIAL_FIRMWARE: Option<&'static [u8]> = None;
#[cfg(feature = "include_hyperdebug_firmware")]
const OFFICIAL_FIRMWARE: Option<&'static [u8]> = Some(include_bytes!(env!("hyperdebug_firmware")));

pub fn official_firmware_version() -> Result<Option<&'static str>> {
    if let Some(fw) = OFFICIAL_FIRMWARE {
        Ok(Some(get_hyperdebug_firmware_version(fw)?))
    } else {
        Ok(None)
    }
}

/// Helper method to verify that the given binary image looks like a HyperDebug firmware image.
fn validate_firmware_image(firmware: &[u8]) -> Result<()> {
    get_hyperdebug_firmware_version(firmware)?;
    Ok(())
}

const EC_COOKIE: [u8; 4] = [0x99, 0x88, 0x77, 0xce];
const EC_FIRMWARE_NAME_LEN: usize = 32;

fn get_hyperdebug_firmware_version(firmware: &[u8]) -> Result<&str> {
    let Some(pos) = firmware[0..1024]
        .chunks(4)
        .position(|c| c[0..4] == EC_COOKIE) else {
            bail!(TransportError::FirmwareProgramFailed(
                "File is not a HyperDebug firmware image".to_string()
            ));
        };
    let firmware_name_field = &firmware[(pos + 1) * 4..(pos + 1) * 4 + EC_FIRMWARE_NAME_LEN];
    let end = firmware_name_field
        .iter()
        .rev()
        .position(|b| *b != 0x00)
        .map(|j| EC_FIRMWARE_NAME_LEN - j)
        .unwrap_or(0);
    Ok(std::str::from_utf8(&firmware_name_field[0..end])?)
}

/// Helper method to perform flash programming using ST's DfuSe variant of the DFU protocol.
/// This method is used both by the `Hyperdebug` and the `HyperdebugDfu` structs.
pub fn update_firmware(
    usb_device: &mut UsbBackend,
    current_firmware_version: Option<&str>,
    firmware: &Option<Vec<u8>>,
    progress: &dyn ProgressIndicator,
    force: bool,
) -> Result<Option<Box<dyn Annotate>>> {
    let firmware: &[u8] = if let Some(vec) = firmware.as_ref() {
        validate_firmware_image(vec)?;
        vec
    } else {
        OFFICIAL_FIRMWARE.ok_or_else(|| anyhow!("No build-in firmware, use --filename"))?
    };

    if !force {
        if let Some(current_version) = current_firmware_version {
            let new_version = get_hyperdebug_firmware_version(firmware)?;
            if new_version == current_version {
                log::warn!(
                    "HyperDebug already running firmware version {}.  Consider --force.",
                    new_version,
                );
                return Ok(None);
            }
        }
    }

    let dfu_desc = scan_usb_descriptor(usb_device)?;

    // Exclusively claim DFU interface, preparing for control requests.
    usb_device.claim_interface(dfu_desc.dfu_interface)?;

    if wait_for_idle(usb_device, dfu_desc.dfu_interface)? != DFU_STATE_APP_IDLE {
        // Device is already running DFU bootloader, proceed to firmware transfer.
        do_update_firmware(usb_device, dfu_desc, firmware, progress)?;
        return Ok(None);
    }

    // Device is running the HyperDebug firmware, not DFU bootloader.  Ask for switch to
    // bootloader, and then restablish USB connection.  Switching is expected to cause loss of USB
    // connection, so we ignore any errors.
    log::info!("Requesting switch to DFU mode...");
    let _ = usb_device
        .write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Class,
                rusb::Recipient::Interface,
            ),
            USB_DFU_DETACH,
            1000,
            dfu_desc.dfu_interface as u16,
            &[],
        )
        .and_then(|_| wait_for_idle(usb_device, dfu_desc.dfu_interface));

    // We get here most likely as a result of an `Err()` from the above block, as the device reset
    // and disconnected from the USB bus.  Wait a little while, and then attempt to establish
    // connection with the DFU bootloader, which will appear with STM DID:VID (not Google's), but
    // same serial number as before.
    std::thread::sleep(std::time::Duration::from_millis(1000));
    log::info!("Connecting to DFU bootloader...");
    let mut dfu_device = UsbBackend::new(
        VID_ST_MICROELECTRONICS,
        PID_DFU_BOOTLOADER,
        Some(usb_device.get_serial_number()),
    )?;
    log::info!("Connected to DFU bootloader");

    let dfu_desc = scan_usb_descriptor(&dfu_device)?;
    dfu_device.claim_interface(dfu_desc.dfu_interface)?;
    do_update_firmware(&dfu_device, dfu_desc, firmware, progress)?;

    // At this point, the new firmware has been completely transferred, and the USB device is
    // resetting and booting the new firmware.  Wait a second, then verify that device can now be
    // found on the USB bus with the original DID:VID.
    std::thread::sleep(std::time::Duration::from_millis(1000));
    log::info!("Connecting to newly flashed firmware...");
    let _new_device = UsbBackend::new(
        usb_device.get_vendor_id(),
        usb_device.get_product_id(),
        Some(usb_device.get_serial_number()),
    )
    .context("Unable to establish connection after flashing.  Possibly bad image.")?;
    Ok(None)
}

fn do_update_firmware(
    usb_device: &UsbBackend,
    dfu_desc: DfuDescriptor,
    firmware: &[u8],
    progress: &dyn ProgressIndicator,
) -> Result<()> {
    let DfuDescriptor {
        dfu_interface,
        xfer_size,
        page_size,
        flash_size,
        base_address,
    } = dfu_desc;

    if page_size == 0 || flash_size != 0x80000 || xfer_size == 0 {
        bail!(TransportError::UsbOpenError(
            "Unrecognized DFU layout (not a Nucleo-L552ZE?)".to_string()
        ));
    }

    log::info!("Erasing flash storage...");
    let firmware_len = firmware.len() as u32;
    progress.new_stage("Erasing", firmware_len as usize);
    let mut bytes_erased: u32 = 0;
    while bytes_erased < firmware_len {
        let mut request = [0u8; 5];
        request[0] = DFUSE_ERASE_PAGE;
        request[1..5].copy_from_slice(&(base_address + bytes_erased).to_le_bytes());
        usb_device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Class,
                rusb::Recipient::Interface,
            ),
            USB_DFU_DNLOAD,
            0,
            dfu_interface as u16,
            &request,
        )?;
        wait_for_idle(usb_device, dfu_interface)?;
        bytes_erased += page_size;
        progress.progress(bytes_erased as usize);
    }

    log::info!("Programming flash storage...");
    progress.new_stage("Writing", firmware_len as usize);
    let mut bytes_sent: u32 = 0;
    while bytes_sent < firmware_len {
        let chunk_size = std::cmp::min(firmware_len - bytes_sent, xfer_size);

        let mut request = [0u8; 5];
        request[0] = DFUSE_PROGRAM_PAGE;
        request[1..5].copy_from_slice(&(base_address + bytes_sent).to_le_bytes());
        usb_device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Class,
                rusb::Recipient::Interface,
            ),
            USB_DFU_DNLOAD,
            0,
            dfu_interface as u16,
            &request,
        )?;
        wait_for_idle(usb_device, dfu_interface)?;

        usb_device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Class,
                rusb::Recipient::Interface,
            ),
            USB_DFU_DNLOAD,
            2,
            dfu_interface as u16,
            &firmware[bytes_sent as usize..(bytes_sent + chunk_size) as usize],
        )?;
        wait_for_idle(usb_device, dfu_interface)?;
        bytes_sent += chunk_size;
        progress.progress(bytes_sent as usize);
    }

    // Request to leave DFU bootloader, and transfer control to newly flashed firmware.
    usb_device.write_control(
        rusb::request_type(
            rusb::Direction::Out,
            rusb::RequestType::Class,
            rusb::Recipient::Interface,
        ),
        USB_DFU_DNLOAD,
        0,
        dfu_interface as u16,
        &[],
    )?;
    // The device resetting will cause USB error here (STM32L5 devices do not execute the request
    // to transfer control until queried for its status, so we have to query).
    let _ = wait_for_idle(usb_device, dfu_interface);
    Ok(())
}

struct DfuDescriptor {
    dfu_interface: u8,
    xfer_size: u32,
    page_size: u32,
    flash_size: u32,
    base_address: u32,
}

/// Inspect USB interface descriptors, looking for DFU-related ones.
fn scan_usb_descriptor(usb_device: &UsbBackend) -> Result<DfuDescriptor> {
    let mut dfu_interface = 0;
    let mut xfer_size = 0;
    let mut page_size = 0;
    let mut flash_size = 0;
    let mut base_address = 0;

    let config_desc = usb_device.active_config_descriptor()?;
    for interface in config_desc.interfaces() {
        for interface_desc in interface.descriptors() {
            let idx = match interface_desc.description_string_index() {
                Some(idx) => idx,
                None => continue,
            };
            let interface_name = match usb_device.read_string_descriptor_ascii(idx) {
                Ok(interface_name) => interface_name,
                _ => continue,
            };
            if interface_desc.class_code() != USB_CLASS_APP
                || interface_desc.sub_class_code() != USB_SUBCLASS_DFU
                || (interface_desc.protocol_code() != 0x01
                    && interface_desc.protocol_code() != 0x02)
            {
                continue;
            }
            dfu_interface = interface.number();
            if let Some(extra_bytes) = interface_desc.extra() {
                // Extra bytes contains inforation encoded according to DFU specification.
                if extra_bytes.len() >= 9 {
                    xfer_size = extra_bytes[5] as u32 | (extra_bytes[6] as u32) << 8;
                }
            }
            static DFU_SECTION_REGEX: Lazy<Regex> = Lazy::new(|| {
                Regex::new("^@([^/]*)/0x([0-9a-fA-F]+)/([0-9]+)\\*([0-9]+)(..)").unwrap()
            });
            let Some(captures) = DFU_SECTION_REGEX.captures(&interface_name) else {
                continue;
            };
            let section_name = captures.get(1).unwrap().as_str().trim();
            if section_name != "Internal Flash" {
                continue;
            }
            // We have the string describing the flash section (as opposed to fuses or
            // once-programmable section), extract the relevant information.
            base_address = u32::from_str_radix(captures.get(2).unwrap().as_str(), 16).unwrap();
            let num_pages = captures.get(3).unwrap().as_str().parse::<u32>().unwrap();
            page_size = captures.get(4).unwrap().as_str().parse::<u32>().unwrap();
            let suffix = captures.get(5).unwrap().as_str();
            if suffix.starts_with('K') {
                page_size *= 1024;
            }
            flash_size = num_pages * page_size;
        }
    }
    Ok(DfuDescriptor {
        dfu_interface,
        xfer_size,
        page_size,
        flash_size,
        base_address,
    })
}

/// Poll the bootloader using GETSTATUS request, until it leaves the "busy" state.
fn wait_for_idle(dfu_device: &UsbBackend, dfu_interface: u8) -> Result<u8> {
    loop {
        let mut response = [0u8; 6];
        let rc = dfu_device.read_control(
            rusb::request_type(
                rusb::Direction::In,
                rusb::RequestType::Class,
                rusb::Recipient::Interface,
            ),
            USB_DFU_GETSTATUS,
            0,
            dfu_interface as u16,
            &mut response,
        )?;
        if rc != response.len() {
            bail!(TransportError::FirmwareProgramFailed("".to_string()));
        }
        let command_status = response[0];
        let minimum_delay_ms =
            u64::from_le_bytes([response[1], response[2], response[3], 0, 0, 0, 0, 0]);
        let device_state = response[4];
        if command_status != DFU_STATUS_OK {
            bail!(TransportError::FirmwareProgramFailed(format!(
                "Unexpected DFU status {}",
                response[0]
            )));
        }
        if device_state == DFU_STATE_APP_IDLE
            || device_state == DFU_STATE_DFU_IDLE
            || device_state == DFU_STATE_DOWNLOAD_IDLE
        {
            return Ok(device_state);
        } else if device_state == DFU_STATE_DOWNLOAD_BUSY {
            std::thread::sleep(std::time::Duration::from_millis(minimum_delay_ms));
        } else {
            bail!(TransportError::FirmwareProgramFailed(format!(
                "Unexpected DFU state {}",
                response[4]
            )));
        }
    }
}
