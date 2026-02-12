// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::with_unknown;
use anyhow::Result;
use zerocopy::{FromBytes, Immutable, IntoBytes};

with_unknown! {
    #[derive(FromBytes, Immutable, IntoBytes)]
    pub enum DfuState: u8 [default = Self::AppIdle] {
      AppIdle = 0,
      AppDetach= 1,
      Idle = 2,
      DnLoadSync = 3,
      DnLoadBusy = 4,
      DnLoadIdle = 5,
      ManifestSync = 6,
      Manifest = 7,
      ManifestWaitReset = 8,
      UpLoadIdle = 9,
      Error = 10,
    }
}

with_unknown! {
    #[derive(FromBytes, Immutable, IntoBytes)]
    pub enum DfuError: u8 [default = Self::Ok] {
      Ok = 0,
      Target = 1,
      File = 2,
      Write = 3,
      Erase = 4,
      CheckErased = 5,
      Prog = 6,
      Verify = 7,
      Address = 8,
      NotDone = 9,
      Firmware = 10,
      Vendor = 11,
      UsbReset = 12,
      PowerOnReset = 13,
      Unknown = 14,
      StalledPkt = 15,
    }
}

with_unknown! {
    pub enum DfuRequest: u8 {
      Detach = 0,
      DnLoad = 1,
      UpLoad = 2,
      GetStatus = 3,
      ClrStatus = 4,
      GetState = 5,
      Abort = 6,
      BusReset = 7,
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum DfuRequestType {
    Out = 0x21,    // direction=out, type=class, recipient=interface.
    In = 0xA1,     // direction=in, type=class, recipient=interface.
    Vendor = 0x40, // direction=out, type=vendor, recipient=device.
}

impl From<DfuRequestType> for u8 {
    fn from(val: DfuRequestType) -> Self {
        val as u8
    }
}

#[derive(Clone, FromBytes, Immutable, IntoBytes, Default)]
#[repr(C)]
pub struct DfuStatus {
    status: DfuError,
    poll_timeout: [u8; 3],
    state: DfuState,
    string: u8,
}

impl std::error::Error for DfuError {}

impl DfuStatus {
    pub fn status(&self) -> std::result::Result<(), DfuError> {
        match self.status {
            DfuError::Ok => Ok(()),
            e => Err(e),
        }
    }
    pub fn poll_timeout(&self) -> u32 {
        u32::from_le_bytes([
            self.poll_timeout[0],
            self.poll_timeout[1],
            self.poll_timeout[2],
            0,
        ])
    }
    pub fn state(&self) -> DfuState {
        self.state
    }
    pub fn string(&self) -> u8 {
        self.string
    }
}

pub trait DfuOperations {
    fn write_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        data: &[u8],
    ) -> Result<usize>;

    fn read_control(
        &self,
        request_type: u8,
        request: u8,
        value: u16,
        index: u16,
        data: &mut [u8],
    ) -> Result<usize>;

    fn get_interface(&self) -> u8;

    /// Download (send) a block to the target device.
    fn download(&self, data: &[u8]) -> Result<usize> {
        self.write_control(
            DfuRequestType::Out.into(),
            DfuRequest::DnLoad.into(),
            /*wValue=*/ 0,
            /*wIndex=*/ self.get_interface() as u16,
            data,
        )
    }

    /// Upload (receive) a block from the target device.
    fn upload(&self, data: &mut [u8]) -> Result<usize> {
        self.read_control(
            DfuRequestType::In.into(),
            DfuRequest::UpLoad.into(),
            /*wValue=*/ 0,
            /*wIndex=*/ self.get_interface() as u16,
            data,
        )
    }

    /// Get the current DFU state.
    fn get_state(&self) -> Result<DfuState> {
        let mut buffer = [0u8];
        self.read_control(
            DfuRequestType::In.into(),
            DfuRequest::GetState.into(),
            /*wValue=*/ 0,
            /*wIndex=*/ self.get_interface() as u16,
            &mut buffer,
        )?;
        Ok(DfuState(buffer[0]))
    }

    /// Get the DFU status.
    fn get_status(&self) -> Result<DfuStatus> {
        let mut status = DfuStatus::default();
        self.read_control(
            DfuRequestType::In.into(),
            DfuRequest::GetStatus.into(),
            /*wValue=*/ 0,
            /*wIndex=*/ self.get_interface() as u16,
            status.as_mut_bytes(),
        )?;
        Ok(status)
    }

    /// Clear the DFU status.
    fn clear_status(&self) -> Result<()> {
        self.write_control(
            DfuRequestType::Out.into(),
            DfuRequest::ClrStatus.into(),
            /*wValue=*/ 0,
            /*wIndex=*/ self.get_interface() as u16,
            &[],
        )?;
        Ok(())
    }

    /// Abort a DFU operation.
    fn abort(&self) -> Result<()> {
        self.write_control(
            DfuRequestType::Out.into(),
            DfuRequest::Abort.into(),
            /*wValue=*/ 0,
            /*wIndex=*/ self.get_interface() as u16,
            &[],
        )?;
        Ok(())
    }
}
