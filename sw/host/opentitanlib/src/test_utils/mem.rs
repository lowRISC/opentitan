// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use arrayvec::ArrayVec;
use std::time::Duration;

use crate::io::uart::Uart;
use crate::test_utils::e2e_command::TestCommand;
use crate::test_utils::rpc::{UartRecv, UartSend};
use crate::test_utils::status::Status;

// Bring in the auto-generated sources.
include!(env!("mem"));

impl MemRead32Req {
    pub fn execute(uart: &dyn Uart, address: u32) -> Result<u32> {
        TestCommand::MemRead32.send(uart)?;
        let op = MemRead32Req { address };
        op.send(uart)?;
        let resp = MemRead32Resp::recv(uart, Duration::from_secs(300), false)?;
        Ok(resp.value)
    }
}

impl MemReadReq {
    pub fn execute(uart: &dyn Uart, start_address: u32, data: &mut [u8]) -> Result<()> {
        let bytes_to_read = data.len();
        let mut bytes_read = 0_usize;
        while bytes_read < bytes_to_read {
            let size_check = MemReadResp {
                data_len: 0,
                data: ArrayVec::new(),
            };
            let op_size = std::cmp::min(bytes_to_read - bytes_read, size_check.data.capacity());
            TestCommand::MemRead.send(uart)?;
            let op = MemReadReq {
                address: start_address + (bytes_read as u32),
                data_len: op_size.try_into().unwrap(),
            };
            op.send(uart)?;
            let resp = MemReadResp::recv(uart, Duration::from_secs(300), false)?;
            data[bytes_read..(bytes_read + op_size)].copy_from_slice(resp.data.as_slice());
            bytes_read += op_size;
        }
        Ok(())
    }
}

impl MemWrite32Req {
    pub fn execute(uart: &dyn Uart, address: u32, value: u32) -> Result<()> {
        TestCommand::MemWrite32.send(uart)?;
        let op = MemWrite32Req { address, value };
        op.send(uart)?;
        Status::recv(uart, Duration::from_secs(300), false)?;
        Ok(())
    }
}

impl MemWriteReq {
    pub fn execute(uart: &dyn Uart, start_address: u32, data: &[u8]) -> Result<()> {
        let bytes_to_write = data.len();
        let mut bytes_written = 0_usize;
        while bytes_written < bytes_to_write {
            TestCommand::MemWrite.send(uart)?;
            let mut op = MemWriteReq {
                address: start_address + (bytes_written as u32),
                data_len: 0,
                data: ArrayVec::new(),
            };
            let op_size = std::cmp::min(bytes_to_write - bytes_written, op.data.capacity());
            op.data
                .try_extend_from_slice(&data[bytes_written..(bytes_written + op_size)])?;
            op.data_len = op_size.try_into().unwrap();
            op.send(uart)?;
            let _ = Status::recv(uart, Duration::from_secs(300), false)?;
            bytes_written += op_size;
        }
        Ok(())
    }
}
