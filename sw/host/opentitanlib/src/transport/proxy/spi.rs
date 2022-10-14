// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::rc::Rc;

use super::ProxyError;
use crate::io::spi::{
    AssertChipSelect, SpiError, Target, TargetChipDeassert, Transfer, TransferMode,
};
use crate::proxy::protocol::{
    Request, Response, SpiRequest, SpiResponse, SpiTransferRequest, SpiTransferResponse,
};
use crate::transport::proxy::{Inner, Proxy};
use crate::util::voltage::Voltage;

pub struct ProxySpi {
    inner: Rc<Inner>,
    instance: String,
}

impl ProxySpi {
    pub fn open(proxy: &Proxy, instance: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&proxy.inner),
            instance: instance.to_string(),
        };
        Ok(result)
    }

    // Convenience method for issuing SPI commands via proxy protocol.
    fn execute_command(&self, command: SpiRequest) -> Result<SpiResponse> {
        match self.inner.execute_command(Request::Spi {
            id: self.instance.clone(),
            command,
        })? {
            Response::Spi(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl Target for ProxySpi {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        match self.execute_command(SpiRequest::GetTransferMode)? {
            SpiResponse::GetTransferMode { mode } => Ok(mode),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_transfer_mode(&self, mode: TransferMode) -> Result<()> {
        match self.execute_command(SpiRequest::SetTransferMode { mode })? {
            SpiResponse::SetTransferMode => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        match self.execute_command(SpiRequest::GetBitsPerWord)? {
            SpiResponse::GetBitsPerWord { bits_per_word } => Ok(bits_per_word),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        match self.execute_command(SpiRequest::SetBitsPerWord { bits_per_word })? {
            SpiResponse::SetBitsPerWord => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_max_speed(&self) -> Result<u32> {
        match self.execute_command(SpiRequest::GetMaxSpeed)? {
            SpiResponse::GetMaxSpeed { speed } => Ok(speed),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
    fn set_max_speed(&self, value: u32) -> Result<()> {
        match self.execute_command(SpiRequest::SetMaxSpeed { value })? {
            SpiResponse::SetMaxSpeed => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        match self.execute_command(SpiRequest::GetMaxTransferCount)? {
            SpiResponse::GetMaxTransferCount { number } => Ok(number as usize),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn max_chunk_size(&self) -> Result<usize> {
        match self.execute_command(SpiRequest::GetMaxChunkSize)? {
            SpiResponse::GetMaxChunkSize { size } => Ok(size as usize),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_voltage(&self, voltage: Voltage) -> Result<()> {
        match self.execute_command(SpiRequest::SetVoltage { voltage })? {
            SpiResponse::SetVoltage => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn run_transaction(&self, transaction: &mut [Transfer]) -> Result<()> {
        let mut req: Vec<SpiTransferRequest> = Vec::new();
        for transfer in transaction.iter() {
            match transfer {
                Transfer::Read(rbuf) => req.push(SpiTransferRequest::Read {
                    len: rbuf.len() as u32,
                }),
                Transfer::Write(wbuf) => req.push(SpiTransferRequest::Write {
                    data: wbuf.to_vec(),
                }),
                Transfer::Both(wbuf, rbuf) => {
                    ensure!(
                        rbuf.len() == wbuf.len(),
                        SpiError::MismatchedDataLength(wbuf.len(), rbuf.len())
                    );
                    req.push(SpiTransferRequest::Both {
                        data: wbuf.to_vec(),
                    })
                }
            }
        }
        match self.execute_command(SpiRequest::RunTransaction { transaction: req })? {
            SpiResponse::RunTransaction { transaction: resp } => {
                ensure!(
                    resp.len() == transaction.len(),
                    ProxyError::UnexpectedReply()
                );
                for pair in resp.iter().zip(transaction.iter_mut()) {
                    match pair {
                        (SpiTransferResponse::Read { data }, Transfer::Read(rbuf))
                        | (SpiTransferResponse::Both { data }, Transfer::Both(_, rbuf)) => {
                            rbuf.clone_from_slice(data);
                        }
                        (SpiTransferResponse::Write, Transfer::Write(_)) => (),
                        _ => bail!(ProxyError::UnexpectedReply()),
                    }
                }
                Ok(())
            }
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn assert_cs(self: Rc<Self>) -> Result<AssertChipSelect> {
        match self.execute_command(SpiRequest::AssertChipSelect)? {
            SpiResponse::AssertChipSelect => Ok(AssertChipSelect::new(self)),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl TargetChipDeassert for ProxySpi {
    fn deassert_cs(&self) {
        match self
            .execute_command(SpiRequest::DeassertChipSelect)
            .expect("Error deactivating chip select")
        {
            SpiResponse::DeassertChipSelect => (),
            _ => panic!("Error deactivating chip select"),
        }
    }
}
