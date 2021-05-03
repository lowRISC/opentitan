use nix::libc::c_int;
use nix::poll;
use std::cmp;
use std::io::{Error, ErrorKind, Result};
use std::os::unix::io::AsRawFd;
use std::time::Duration;

/// Waits for an event on `fd` or for `timeout` to expire.
pub fn wait_timeout<FD: AsRawFd>(
    fd: &FD,
    events: poll::PollFlags,
    timeout: Duration,
) -> Result<()> {
    let timeout = cmp::min(timeout.as_millis(), c_int::max_value() as u128) as c_int;

    let mut pfd = [poll::PollFd::new(fd.as_raw_fd(), events)];
    let retval = poll::poll(&mut pfd, timeout).map_err(|e| Error::new(ErrorKind::Other, e))?;
    if retval == 0 {
        Err(Error::new(
            ErrorKind::TimedOut,
            "timed out waiting for fd to be ready",
        ))
    } else {
        Ok(())
    }
}

/// Waits for `fd` to become ready to read or `timeout` to expire.
pub fn wait_read_timeout<FD: AsRawFd>(fd: &FD, timeout: Duration) -> Result<()> {
    wait_timeout(fd, poll::PollFlags::POLLIN, timeout)
}
