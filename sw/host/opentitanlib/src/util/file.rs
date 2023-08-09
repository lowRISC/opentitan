// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use nix::libc::c_int;
use nix::poll;
use pem_rfc7468::{Decoder, Encoder, LineEnding};
use thiserror::Error;

use std::convert::TryInto;
use std::fs::File;
use std::io::{self, Read, Write};
use std::os::fd::{AsFd, BorrowedFd};
use std::os::unix::io::AsRawFd;
use std::path::Path;
use std::time::Duration;

/// Error type for errors related to PEM serialization.
#[derive(Debug, Error)]
enum PemError {
    #[error("PEM type error; expecting {0:?} but got {1:?}")]
    LabelError(&'static str, String),
}

/// Trait for data that can be written to and read from PEM files.
pub trait PemSerilizable: ToWriter + FromReader {
    /// The label for the PEM file.
    ///
    /// Appears around the base64 encoded data.
    /// -----BEGIN MY_LABEL-----
    /// ...
    /// -----END MY_LABEL-----
    fn label() -> &'static str;

    /// Write to PEM file with label from `Self::label()`.
    fn write_pem_file(&self, path: &Path) -> Result<()> {
        const MAX_PEM_SIZE: usize = 4096;

        let mut bytes = Vec::<u8>::new();
        self.to_writer(&mut bytes)?;

        let mut buf = [0u8; MAX_PEM_SIZE];
        let mut encoder = Encoder::new(Self::label(), LineEnding::LF, &mut buf)?;
        encoder.encode(&bytes)?;
        let len = encoder.finish()?;

        let mut file = File::create(path)?;
        Ok(file.write_all(&buf[..len])?)
    }

    /// Read in from PEM file, ensuring the label matches `Self::label()`.
    fn read_pem_file(path: &Path) -> Result<Self> {
        let mut file = File::open(path)?;
        let mut pem = Vec::<u8>::new();
        file.read_to_end(&mut pem)?;

        let mut decoder = Decoder::new(&pem)?;
        ensure!(
            decoder.type_label() == Self::label(),
            PemError::LabelError(Self::label(), decoder.type_label().to_owned()),
        );

        let mut buf = Vec::new();
        decoder.decode_to_end(&mut buf)?;

        Self::from_reader(buf.as_slice())
    }
}

/// Trait for data types that can be streamed to a reader.
pub trait FromReader: Sized {
    /// Reads in an instance of `Self`.
    fn from_reader(r: impl Read) -> Result<Self>;

    /// Reads an instance of `Self` from a binary file at `path`.
    fn read_from_file(path: &Path) -> Result<Self> {
        let file = File::open(path)?;
        Self::from_reader(file)
    }
}

/// Trait for data types that can be written to a writer.
pub trait ToWriter: Sized {
    /// Writes out `self`.
    fn to_writer(&self, w: &mut impl Write) -> Result<()>;

    /// Writes `self` to a file at `path` in binary format.
    fn write_to_file(self, path: &Path) -> Result<()> {
        let mut file = File::create(path)?;
        self.to_writer(&mut file)
    }
}

/// Waits for an event on `fd` or for `timeout` to expire.
pub fn wait_timeout(fd: BorrowedFd<'_>, events: poll::PollFlags, timeout: Duration) -> Result<()> {
    let timeout = timeout.as_millis().try_into().unwrap_or(c_int::MAX);
    let mut pfd = [poll::PollFd::new(fd.as_raw_fd(), events)];
    match poll::poll(&mut pfd, timeout)? {
        0 => Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "timed out waiting for fd to be ready",
        )
        .into()),
        _ => Ok(()),
    }
}

/// Waits for `fd` to become ready to read or `timeout` to expire.
pub fn wait_read_timeout(fd: &impl AsFd, timeout: Duration) -> Result<()> {
    wait_timeout(fd.as_fd(), poll::PollFlags::POLLIN, timeout)
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::bail;
    use nix::sys::socket::{socketpair, AddressFamily, SockFlag, SockType};
    use nix::unistd::{read, write};
    use std::os::fd::{FromRawFd, OwnedFd};

    #[test]
    fn test_data_ready() -> Result<()> {
        let (snd, rcv) = socketpair(
            AddressFamily::Unix,
            SockType::Stream,
            None,
            SockFlag::empty(),
        )?;
        let snd = unsafe { OwnedFd::from_raw_fd(snd) };
        let rcv = unsafe { OwnedFd::from_raw_fd(rcv) };

        // Send the test data into the socket.
        let sndbuf = b"abc123";
        assert_eq!(write(snd.as_raw_fd(), sndbuf)?, sndbuf.len());

        // Wait for it to be ready.
        wait_read_timeout(&rcv, Duration::from_millis(10))?;

        // Receive the test data and compare.
        let mut rcvbuf = [0u8; 6];
        assert_eq!(read(rcv.as_raw_fd(), &mut rcvbuf)?, sndbuf.len());
        assert_eq!(sndbuf, &rcvbuf);
        Ok(())
    }

    #[test]
    fn test_timeout() -> Result<()> {
        let (_snd, rcv) = socketpair(
            AddressFamily::Unix,
            SockType::Stream,
            None,
            SockFlag::empty(),
        )?;
        let rcv = unsafe { OwnedFd::from_raw_fd(rcv) };

        // Expect to timeout since there is no data ready on the socket.
        let result = wait_read_timeout(&rcv, Duration::from_millis(10));
        assert!(result.is_err());
        let err = result.unwrap_err();
        match err.downcast_ref::<io::Error>() {
            Some(e) => assert_eq!(io::ErrorKind::TimedOut, e.kind()),
            _ => bail!("Unexpected error result {:?}", err),
        }
        Ok(())
    }
}
