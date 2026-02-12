// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::ffi::OsStr;
use std::io::Write;
use std::pin::Pin;
use std::task::{Poll, ready};

use anyhow::{Context, Result, anyhow};
use tokio::io::AsyncRead;

use crate::io::console::ConsoleDevice;
use crate::util::runtime::MultiWaker;

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
pub struct ChildConsole {
    child: RefCell<std::process::Child>,
    stdout: Option<RefCell<tokio::process::ChildStdout>>,
    rd: RefCell<TransferState>,
    wr: RefCell<TransferState>,
    multi_waker: MultiWaker,
}

impl ChildConsole {
    pub fn spawn_corrupt<S: AsRef<OsStr>>(
        argv: &[S],
        rd: TransferState,
        wr: TransferState,
    ) -> Result<Self> {
        let mut command = std::process::Command::new(argv[0].as_ref());
        for arg in &argv[1..] {
            command.arg(arg.as_ref());
        }
        let mut child = command
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::inherit())
            .spawn()?;
        let _runtime_guard = crate::util::runtime().enter();
        let stdout = match child.stdout.take() {
            Some(v) => Some(RefCell::new(tokio::process::ChildStdout::from_std(v)?)),
            None => None,
        };
        Ok(ChildConsole {
            child: RefCell::new(child),
            stdout,
            rd: RefCell::new(rd),
            wr: RefCell::new(wr),
            multi_waker: MultiWaker::new(),
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

impl ConsoleDevice for ChildConsole {
    fn poll_read(&self, cx: &mut std::task::Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        let mut stdout = self
            .stdout
            .as_ref()
            .context("child has no stdout")?
            .borrow_mut();
        let mut read_buf = tokio::io::ReadBuf::new(buf);
        ready!(
            self.multi_waker
                .poll_with(cx, |cx| Pin::new(&mut *stdout).poll_read(cx, &mut read_buf))
        )?;
        let n = read_buf.filled().len();
        let mut rd = self.rd.borrow_mut();
        rd.maybe_corrupt(read_buf.filled_mut());
        Poll::Ready(Ok(n))
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
