// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::{BufWriter, ErrorKind, Read, Write};
use std::net::TcpStream;
use std::rc::Rc;
use thiserror::Error;

use crate::impl_serializable_error;
use crate::io::spi::{AssertChipSelect, MaxSizes, SpiError, Target, Transfer, TransferMode};
use crate::proxy::protocol::{
    Message, Request, Response, SpiRequest, SpiResponse, SpiTransferRequest, SpiTransferResponse,
};
use crate::transport::TransportError;

#[derive(Debug, Error, Serialize, Deserialize)]
pub enum ProxyError {
    #[error("Unexpected reply")]
    UnexpectedReply(),
    #[error("JSON encoding: {0}")]
    JsonEncoding(String),
    #[error("JSON decoding: {0}")]
    JsonDecoding(String),
}
impl_serializable_error!(ProxyError);

/// Represents the verilator virtual SPI.
pub struct VerilatorSpi {
    instance: String,
    use_stream: bool,
    stream: Option<RefCell<TcpStream>>,
    pipe: Option<RefCell<File>>,
    recv_buf: RefCell<Vec<u8>>,
}

impl VerilatorSpi {
    pub fn open(name: &str, instance: &str) -> Result<Self> {
        let ref_pipe;
        let ref_stream;
        let use_stream;

        // check if read_name is in TCP socket or pipe device format
        if name.contains(':') && !name.contains('/') {
            let stream = TcpStream::connect(name)
                .map_err(|e| TransportError::ProxyConnectError(name.to_string(), e.to_string()))?;

            ref_pipe = None;
            ref_stream = Some(RefCell::new(stream));
            use_stream = true;
        } else {
            let pipe = OpenOptions::new()
                .read(true)
                .write(true)
                .open(name)
                .map_err(|e| TransportError::OpenError(name.to_string(), e.to_string()))?;

            ref_pipe = Some(RefCell::new(pipe));
            ref_stream = None;
            use_stream = false;
        }

        Ok(VerilatorSpi {
            instance: instance.to_string(),
            use_stream,
            stream: ref_stream,
            pipe: ref_pipe,
            recv_buf: RefCell::new(Vec::new()),
        })
    }

    // Convenience method for issuing SPI commands via proxy protocol.
    fn execute_command(&self, command: SpiRequest) -> Result<SpiResponse> {
        match self.execute_request(Request::Spi {
            id: self.instance.clone(),
            command,
        })? {
            Response::Spi(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Helper method for sending one JSON request and receiving the response.
    /// Called as part of the spi implementation.
    fn execute_request(&self, req: Request) -> Result<Response> {
        self.send_json_request(req).context("json encoding")?;
        loop {
            match self.recv_json_response().context("json decoding")? {
                Message::Res(res) => match res {
                    Ok(value) => return Ok(value),
                    Err(e) => return Err(anyhow::Error::from(e)),
                },
                Message::Async { channel: _, msg: _ } => {}
                _ => bail!(ProxyError::UnexpectedReply()),
            }
        }
    }

    /// Send a one-line JSON encoded requests over a TCP socker,
    /// terminated with one newline.
    fn send_json_request_stream(&self, req: Request) -> Result<()> {
        if let Some(ref ref_stream) = self.stream {
            let conn: &mut std::net::TcpStream = &mut ref_stream.borrow_mut();
            let mut writer = BufWriter::new(conn);
            serde_json::to_writer(&mut writer, &Message::Req(req))?;
            writer.write_all(&[b'\n'])?;
            writer.flush()?;
        } else {
            return Err(anyhow!("TCP socket not connected")).context("SPI write error");
        }
        Ok(())
    }

    /// Send a one-line JSON encoded requests over a pseudo-terminal pipe,
    /// terminated with one newline.
    fn send_json_request_pipe(&self, req: Request) -> Result<()> {
        if let Some(ref ref_pipe) = self.pipe {
            let conn: &mut std::fs::File = &mut ref_pipe.borrow_mut();
            let mut writer = BufWriter::new(conn);
            serde_json::to_writer(&mut writer, &Message::Req(req))?;
            writer.write_all(&[b'\n'])?;
            writer.flush()?;
        } else {
            return Err(anyhow!("Pipe not opened")).context("SPI write error");
        }
        Ok(())
    }

    /// Send a one-line JSON encoded requests, terminated with one newline.
    fn send_json_request(&self, req: Request) -> Result<()> {
        if self.use_stream {
            self.send_json_request_stream(req)
        } else {
            self.send_json_request_pipe(req)
        }
    }

    /// Decode one JSON response, possibly waiting for more network data.
    fn recv_json_response_stream(&self) -> Result<Message> {
        if let Some(msg) = self.dequeue_json_response()? {
            return Ok(msg);
        }
        if let Some(ref ref_stream) = self.stream {
            let conn: &mut std::net::TcpStream = &mut ref_stream.borrow_mut();
            let mut buf = self.recv_buf.borrow_mut();
            let mut idx: usize = buf.len();
            loop {
                buf.resize(idx + 2048, 0);
                let rc = conn.read(&mut buf[idx..])?;
                if rc == 0 {
                    anyhow::bail!(io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "Server unexpectedly closed connection"
                    ))
                }
                idx += rc;
                let Some(newline_pos) = buf[idx - rc..idx].iter().position(|b| *b == b'\n') else {
                    continue;
                };
                let result = serde_json::from_slice::<Message>(&buf[..idx - rc + newline_pos])?;
                buf.resize(idx, 0u8);
                buf.drain(..idx - rc + newline_pos + 1);
                return Ok(result);
            }
        } else {
            Err(anyhow!("TCP socket not connected")).context("SPI read error")
        }
    }

    /// Decode one JSON response, possibly waiting for more data in pipe.
    fn recv_json_response_pipe(&self) -> Result<Message> {
        if let Some(msg) = self.dequeue_json_response()? {
            return Ok(msg);
        }
        if let Some(ref ref_pipe) = self.pipe {
            let conn: &mut std::fs::File = &mut ref_pipe.borrow_mut();
            let mut buf = self.recv_buf.borrow_mut();
            let mut idx: usize = buf.len();
            loop {
                buf.resize(idx + 2048, 0);
                let rc = conn.read(&mut buf[idx..])?;
                if rc == 0 {
                    anyhow::bail!(io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "Server unexpectedly closed connection"
                    ))
                }
                idx += rc;
                let Some(newline_pos) = buf[idx - rc..idx].iter().position(|b| *b == b'\n') else {
                    continue;
                };
                let result = serde_json::from_slice::<Message>(&buf[..idx - rc + newline_pos])?;
                buf.resize(idx, 0u8);
                buf.drain(..idx - rc + newline_pos + 1);
                return Ok(result);
            }
        } else {
            Err(anyhow!("Pipe not opened")).context("SPI read error")
        }
    }

    /// Decode one JSON response, possibly waiting for more data.
    fn recv_json_response(&self) -> Result<Message> {
        if self.use_stream {
            self.recv_json_response_stream()
        } else {
            self.recv_json_response_pipe()
        }
    }

    fn dequeue_json_response(&self) -> Result<Option<Message>> {
        let mut buf = self.recv_buf.borrow_mut();
        let Some(newline_pos) = buf.iter().position(|b| *b == b'\n') else {
            return Ok(None);
        };
        let result = serde_json::from_slice::<Message>(&buf[..newline_pos])?;
        buf.drain(..newline_pos + 1);
        Ok(Some(result))
    }
}

impl Target for VerilatorSpi {
    fn get_transfer_mode(&self) -> Result<TransferMode> {
        Ok(TransferMode::Mode0)
    }
    fn set_transfer_mode(&self, mode: TransferMode) -> Result<()> {
        log::warn!(
            "set_transfer_mode to {:?}, but only Mode0 is supported on this device",
            mode
        );
        Ok(())
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        Ok(8)
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        match bits_per_word {
            8 => Ok(()),
            _ => Err(SpiError::InvalidWordSize(bits_per_word).into()),
        }
    }

    fn get_max_speed(&self) -> Result<u32> {
        Ok(125_000)
    }
    fn set_max_speed(&self, frequency: u32) -> Result<()> {
        log::warn!(
            "set_max_speed to {:?}, but this device doesn't support changing speeds.",
            frequency
        );
        Ok(())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        Ok(1)
    }

    fn get_max_transfer_sizes(&self) -> Result<MaxSizes> {
        Ok(MaxSizes {
            read: 4096,
            write: 4096,
        })
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
        Err(TransportError::UnsupportedOperation.into())
    }
}
