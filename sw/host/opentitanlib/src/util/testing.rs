// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::io::uart::Uart;
use anyhow::{anyhow, Result};
use std::cell::RefCell;
use std::ffi::OsStr;
use std::io::{Read, Write};
use std::time::Duration;

// The transfer state allows us to intentionally inject errors into
// the data stream to test error handling.
#[derive(Default)]
pub struct TransferState {
    nbytes: usize,
    corrupt: Vec<usize>,
}
impl TransferState {
    pub fn new(corrupt: &[usize]) -> Self {
        TransferState {
            nbytes: 0,
            corrupt: corrupt.to_vec(),
        }
    }
    fn maybe_corrupt(&mut self, buf: &mut [u8]) {
        while !self.corrupt.is_empty() {
            let mut index = self.corrupt[0];
            if index >= self.nbytes && index < self.nbytes + buf.len() {
                index -= self.nbytes;
                buf[index] = !buf[index];
            } else {
                break;
            }
            self.corrupt.remove(0);
        }
        self.nbytes += buf.len();
    }
}
// A convenience wrapper for spawning a child process and
// interacting with its stdin/stdout.
pub struct ChildUart {
    child: RefCell<std::process::Child>,
    rd: RefCell<TransferState>,
    wr: RefCell<TransferState>,
}

impl ChildUart {
    pub fn spawn_corrupt<S: AsRef<OsStr>>(
        argv: &[S],
        rd: TransferState,
        wr: TransferState,
    ) -> Result<Self> {
        let mut command = std::process::Command::new(argv[0].as_ref());
        for arg in &argv[1..] {
            command.arg(arg.as_ref());
        }
        let child = command
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit())
            .spawn()?;
        Ok(ChildUart {
            child: RefCell::new(child),
            rd: RefCell::new(rd),
            wr: RefCell::new(wr),
        })
    }

    pub fn spawn<S: AsRef<OsStr>>(argv: &[S]) -> Result<Self> {
        Self::spawn_corrupt(argv, Default::default(), Default::default())
    }

    pub fn wait(&self) -> Result<std::process::ExitStatus> {
        let mut child = self.child.borrow_mut();
        Ok(child.wait()?)
    }
}

impl Uart for ChildUart {
    fn get_baudrate(&self) -> Result<u32> {
        Err(anyhow!("Not implemented"))
    }
    fn set_baudrate(&self, _baudrate: u32) -> Result<()> {
        Err(anyhow!("Not implemented"))
    }
    fn read_timeout(&self, _buf: &mut [u8], _timeout: Duration) -> Result<usize> {
        Err(anyhow!("Not implemented"))
    }
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        let mut child = self.child.borrow_mut();
        if let Some(stdout) = &mut child.stdout {
            let n = stdout.read(buf)?;
            let mut rd = self.rd.borrow_mut();
            rd.maybe_corrupt(buf);
            Ok(n)
        } else {
            Err(anyhow!("child has no stdout"))
        }
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        let mut child = self.child.borrow_mut();
        if let Some(stdin) = &mut child.stdin {
            let mut data = buf.to_vec();
            let mut wr = self.wr.borrow_mut();
            wr.maybe_corrupt(&mut data);
            stdin.write_all(&data)?;
            Ok(())
        } else {
            Err(anyhow!("child has no stdin"))
        }
    }
}
