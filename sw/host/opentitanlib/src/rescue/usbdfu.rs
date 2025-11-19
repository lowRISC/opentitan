// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use std::cell::{Cell, Ref, RefCell};
use std::time::Duration;

use crate::app::{TransportWrapper, UartRx};
use crate::io::usb::UsbDevice;
use crate::rescue::dfu::*;
use crate::rescue::{EntryMode, Rescue, RescueError, RescueMode, RescueParams};

pub struct UsbDfu {
    usb: RefCell<Option<Box<dyn UsbDevice>>>,
    interface: Cell<u8>,
    params: RescueParams,
    reset_delay: Duration,
    enter_delay: Duration,
}

impl UsbDfu {
    const CLASS: u8 = 254;
    const SUBCLASS: u8 = 1;
    const PROTOCOL: u8 = 2;
    pub fn new(params: RescueParams) -> Self {
        UsbDfu {
            usb: RefCell::new(None),
            interface: Cell::default(),
            params,
            reset_delay: Duration::from_millis(50),
            enter_delay: Duration::from_secs(5),
        }
    }

    fn device(&self) -> Ref<'_, dyn UsbDevice> {
        let usb = self.usb.borrow();
        Ref::map(usb, |d| &**d.as_ref().expect("device handle"))
    }
}

impl Rescue for UsbDfu {
    fn enter(&self, transport: &TransportWrapper, mode: EntryMode) -> Result<()> {
        log::info!(
            "Setting {:?}({}) to trigger rescue mode.",
            self.params.trigger,
            self.params.value
        );
        self.params.set_trigger(transport, true)?;

        match mode {
            EntryMode::Reset => transport.reset_with_delay(UartRx::Keep, self.reset_delay)?,
            EntryMode::Reboot => self.reboot()?,
            EntryMode::None => {}
        }

        let device = transport.usb()?.device_by_interface_with_timeout(
            Self::CLASS,
            Self::SUBCLASS,
            Self::PROTOCOL,
            self.params.usb_serial.as_deref(),
            self.enter_delay,
        );
        log::info!("Rescue triggered; clearing trigger condition.");
        self.params.set_trigger(transport, false)?;
        let device = device?;

        let config = device.active_configuration()?;
        for intf in config.interface_alt_settings() {
            let desc = intf.descriptor()?;
            if desc.class == Self::CLASS
                && desc.subclass == Self::SUBCLASS
                && desc.protocol == Self::PROTOCOL
            {
                device.claim_interface(desc.intf_num)?;
                self.interface.set(desc.intf_num);
                break;
            }
        }
        self.usb.replace(Some(device));
        Ok(())
    }

    fn set_mode(&self, mode: RescueMode) -> Result<()> {
        let setting = match mode {
            // FIXME: the RescueMode to AltSetting values either need to be permanently fixed, or
            // the alt interfaces need to describe themselves via a string descriptor.
            RescueMode::Rescue => 0,
            RescueMode::RescueB => 1,
            RescueMode::DeviceId => 2,
            RescueMode::BootLog => 3,
            RescueMode::BootSvcReq => 4,
            RescueMode::BootSvcRsp => 4,
            RescueMode::OwnerBlock => 5,
            RescueMode::GetOwnerPage0 => 5,
            _ => bail!(RescueError::BadMode(format!(
                "mode {mode:?} not supported by DFU"
            ))),
        };

        let device = self.device();
        log::info!("Mode {mode} is AltSetting {setting}");
        device.set_alternate_setting(self.interface.get(), setting)?;
        Ok(())
    }

    fn set_speed(&self, _speed: u32) -> Result<u32> {
        log::warn!("set_speed is not implemented for DFU");
        Ok(0)
    }

    fn reboot(&self) -> Result<()> {
        let usb = self.device();
        usb.release_interface(self.interface.get())?;
        match usb.reset() {
            Ok(_) => {}
            Err(e) => log::warn!("USB reset: {e}"),
        }
        Ok(())
    }

    fn send(&self, data: &[u8]) -> Result<()> {
        for chunk in data.chunks(2048) {
            let _ = self.download(chunk)?;
            let status = loop {
                let status = self.get_status()?;
                match status.state() {
                    DfuState::DnLoadIdle | DfuState::Error => {
                        break status;
                    }
                    _ => {
                        std::thread::sleep(Duration::from_millis(status.poll_timeout() as u64));
                    }
                }
            };
            status.status()?;
        }
        // Send a zero-length chunk to signal the end.
        let _ = self.download(&[])?;
        let status = self.get_status()?;
        log::warn!("State after DFU download: {}", status.state());
        Ok(())
    }

    fn recv(&self) -> Result<Vec<u8>> {
        let mut data = vec![0u8; 2048];
        /*
         * FIXME: what am I supposed to do here?
         * The spec seems to indicate that I should keep performing `upload` until I get back a
         * short or zero length packet.
        let mut offset = 0;
        loop {
            log::info!("upload at {offset}");
            let length = self.upload(&mut data[offset..])?;
            if length == 0 || length < data.len() - offset {
                break;
            }
            offset += length;
        }
        */
        self.upload(&mut data)?;
        let status = self.get_status()?;
        log::warn!("State after DFU upload: {}", status.state());
        Ok(data)
    }
}

impl DfuOperations for UsbDfu {
    fn write_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        data: &[u8],
    ) -> Result<usize> {
        let usb = self.device();
        usb.write_control(request_type, request, value, index, data)
    }

    fn read_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        data: &mut [u8],
    ) -> Result<usize> {
        let usb = self.device();
        usb.read_control(request_type, request, value, index, data)
    }

    fn get_interface(&self) -> u8 {
        self.interface.get()
    }
}
