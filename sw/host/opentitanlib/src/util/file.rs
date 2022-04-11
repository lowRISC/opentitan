// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use nix::libc::c_int;
use nix::poll;
use std::convert::TryInto;
use std::io;
use std::os::unix::io::{AsRawFd, RawFd};
use std::time::Duration;

/// Waits for an event on `fd` or for `timeout` to expire.
pub fn wait_timeout(fd: RawFd, events: poll::PollFlags, timeout: Duration) -> Result<()> {
    let timeout = timeout.as_millis().try_into().unwrap_or(c_int::MAX);
    let mut pfd = [poll::PollFd::new(fd, events)];
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
pub fn wait_read_timeout(fd: &impl AsRawFd, timeout: Duration) -> Result<()> {
    wait_timeout(fd.as_raw_fd(), poll::PollFlags::POLLIN, timeout)
}

/// Waits for `fd` to become ready to read or `timeout` to expire.
pub fn wait_fd_read_timeout(fd: RawFd, timeout: Duration) -> Result<()> {
    wait_timeout(fd, poll::PollFlags::POLLIN, timeout)
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::bail;
    use nix::sys::socket::{socketpair, AddressFamily, SockFlag, SockType};
    use nix::unistd::{read, write};

    #[test]
    fn test_data_ready() -> Result<()> {
        let (snd, rcv) = socketpair(
            AddressFamily::Unix,
            SockType::Stream,
            None,
            SockFlag::empty(),
        )?;

        // Send the test data into the socket.
        let sndbuf = b"abc123";
        assert_eq!(write(snd, sndbuf)?, sndbuf.len());

        // Wait for it to be ready.
        wait_read_timeout(&rcv, Duration::from_millis(10))?;

        // Receive the test data and compare.
        let mut rcvbuf = [0u8; 6];
        assert_eq!(read(rcv, &mut rcvbuf)?, sndbuf.len());
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
