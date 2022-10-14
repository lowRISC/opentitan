// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::rc::Rc;

use super::ProxyError;
use crate::io::i2c::{Bus, Transfer};
use crate::proxy::protocol::{
    I2cRequest, I2cResponse, I2cTransferRequest, I2cTransferResponse, Request, Response,
};
use crate::transport::proxy::{Inner, Proxy};

pub struct ProxyI2c {
    inner: Rc<Inner>,
    instance: String,
}

impl ProxyI2c {
    pub fn open(proxy: &Proxy, instance: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&proxy.inner),
            instance: instance.to_string(),
        };
        Ok(result)
    }

    // Convenience method for issuing I2C commands via proxy protocol.
    fn execute_command(&self, command: I2cRequest) -> Result<I2cResponse> {
        match self.inner.execute_command(Request::I2c {
            id: self.instance.clone(),
            command,
        })? {
            Response::I2c(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl Bus for ProxyI2c {
    fn run_transaction(&self, address: u8, transaction: &mut [Transfer]) -> Result<()> {
        let mut req: Vec<I2cTransferRequest> = Vec::new();
        for transfer in &*transaction {
            // &* to treat as non-mutable in this loop
            match transfer {
                Transfer::Read(rbuf) => req.push(I2cTransferRequest::Read {
                    len: rbuf.len() as u32,
                }),
                Transfer::Write(wbuf) => req.push(I2cTransferRequest::Write {
                    data: wbuf.to_vec(),
                }),
            }
        }
        match self.execute_command(I2cRequest::RunTransaction {
            address,
            transaction: req,
        })? {
            I2cResponse::RunTransaction { transaction: resp } => {
                ensure!(
                    resp.len() == transaction.len(),
                    ProxyError::UnexpectedReply()
                );
                for pair in resp.iter().zip(transaction.iter_mut()) {
                    match pair {
                        (I2cTransferResponse::Read { data }, Transfer::Read(rbuf)) => {
                            rbuf.clone_from_slice(data);
                        }
                        (I2cTransferResponse::Write, Transfer::Write(_)) => (),
                        _ => bail!(ProxyError::UnexpectedReply()),
                    }
                }
                Ok(())
            }
        }
    }
}
