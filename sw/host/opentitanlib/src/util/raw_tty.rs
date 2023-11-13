// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::{IsTerminal, Read, Result};
use std::ops::{Deref, DerefMut};
use std::os::fd::{AsFd, BorrowedFd};

use rustix::termios::{self, Termios};

/// Raw TTY wrapper over any file descriptor.
///
/// The fd is converted into raw terminal mode and restored to its original state on drop, if it's a terminal.
/// For non-terminal fds, nothing will be performed.
pub struct RawTty<T: AsFd> {
    termios: Option<Termios>,
    fd: T,
}

impl<T: AsFd> Deref for RawTty<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.fd
    }
}

impl<T: AsFd> DerefMut for RawTty<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.fd
    }
}

impl<T: AsFd> AsFd for RawTty<T> {
    fn as_fd(&self) -> BorrowedFd<'_> {
        self.fd.as_fd()
    }
}

impl<T: AsFd + Read> Read for RawTty<T> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.fd.read(buf)
    }
}

impl<T: AsFd> RawTty<T> {
    pub fn new(fd: T) -> Result<Self> {
        let termios = if fd.as_fd().is_terminal() {
            let termios = termios::tcgetattr(&fd)?;

            let mut raw_termios = termios.clone();
            raw_termios.make_raw();
            termios::tcsetattr(&fd, termios::OptionalActions::Now, &raw_termios)?;

            Some(termios)
        } else {
            None
        };

        Ok(Self { termios, fd })
    }
}

impl<T: AsFd> Drop for RawTty<T> {
    fn drop(&mut self) {
        if let Some(termios) = self.termios.as_ref() {
            termios::tcsetattr(&self.fd, termios::OptionalActions::Now, termios).unwrap();
        }
    }
}
