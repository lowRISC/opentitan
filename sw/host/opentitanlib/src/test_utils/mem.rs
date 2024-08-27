// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use std::time::Duration;

use crate::io::console::ConsoleDevice;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
include!(env!("mem"));

impl MemRead32Req {
    pub fn execute<T>(device: &T, address: u32) -> Result<u32>
    where
        T: ConsoleDevice + ?Sized,
    {
        TestCommand::MemRead32.send_with_crc(device)?;
        let op = MemRead32Req { address };
        op.send_with_crc(device)?;
        let resp = MemRead32Resp::recv(device, Duration::from_secs(300), false)?;
        Ok(resp.value)
    }
}

impl MemReadReq {
    pub fn execute<T>(device: &T, start_address: u32, data: &mut [u8]) -> Result<()>
    where
        T: ConsoleDevice + ?Sized,
    {
        let bytes_to_read = data.len();
        let mut bytes_read = 0_usize;
        while bytes_read < bytes_to_read {
            let size_check = MemReadResp {
                data_len: 0,
                data: ArrayVec::new(),
            };
            let op_size = std::cmp::min(bytes_to_read - bytes_read, size_check.data.capacity());
            TestCommand::MemRead.send_with_crc(device)?;
            let op = MemReadReq {
                address: start_address + (bytes_read as u32),
                data_len: op_size.try_into().unwrap(),
            };
            op.send_with_crc(device)?;
            let resp = MemReadResp::recv(device, Duration::from_secs(300), false)?;
            data[bytes_read..(bytes_read + op_size)].copy_from_slice(resp.data.as_slice());
            bytes_read += op_size;
        }
        Ok(())
    }
}

impl MemWrite32Req {
    pub fn execute<T>(device: &T, address: u32, value: u32) -> Result<()>
    where
        T: ConsoleDevice + ?Sized,
    {
        TestCommand::MemWrite32.send_with_crc(device)?;
        let op = MemWrite32Req { address, value };
        op.send_with_crc(device)?;
        Status::recv(device, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl MemWriteReq {
    pub fn execute<T>(device: &T, start_address: u32, data: &[u8]) -> Result<()>
    where
        T: ConsoleDevice + ?Sized,
    {
        let bytes_to_write = data.len();
        let mut bytes_written = 0_usize;
        while bytes_written < bytes_to_write {
            TestCommand::MemWrite.send_with_crc(device)?;
            let mut op = MemWriteReq {
                address: start_address + (bytes_written as u32),
                data_len: 0,
                data: ArrayVec::new(),
            };
            let op_size = std::cmp::min(bytes_to_write - bytes_written, op.data.capacity());
            op.data
                .try_extend_from_slice(&data[bytes_written..(bytes_written + op_size)])?;
            op.data_len = op_size.try_into().unwrap();
            op.send_with_crc(device)?;
            let _ = Status::recv(device, Duration::from_secs(300), false)?;
            bytes_written += op_size;
        }
        Ok(())
    }
}
