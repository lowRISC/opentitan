// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::{Context, Result};

use super::ConsoleDevice;
use crate::io::console::ConsoleError;

/// Extension trait to [`Uart`] where useful methods are provided.
pub trait ConsoleExt {
    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function is blocking.
    fn read(&self, buf: &mut [u8]) -> Result<usize>;

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize>;

    /// Wait for a line that matches the specified pattern to appear.
    ///
    /// The line read is returned.
    fn wait_for_line(&self, pattern: impl MatchPattern, timeout: Duration) -> Result<Vec<u8>>;
}

impl<T: ConsoleDevice + ?Sized> ConsoleExt for T {
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        crate::util::runtime::block_on(std::future::poll_fn(|cx| self.poll_read(cx, buf)))
    }

    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        crate::util::runtime::block_on(async {
            tokio::time::timeout(timeout, std::future::poll_fn(|cx| self.poll_read(cx, buf))).await
        })
        .unwrap_or(Ok(0))
    }

    fn wait_for_line(&self, pattern: impl MatchPattern, timeout: Duration) -> Result<Vec<u8>> {
        crate::util::runtime::block_on(async {
            tokio::time::timeout(timeout, async {
                loop {
                    let line = read_line(self).await?;
                    if pattern.is_match(&line) {
                        return Ok(line);
                    }
                }
            })
            .await
            .with_context(|| ConsoleError::TimedOut)?
        })
    }
}

async fn read_line<T: ConsoleDevice + ?Sized>(console: &T) -> Result<Vec<u8>> {
    let mut buf = Vec::new();

    loop {
        // Read one byte at a time to avoid the risk of consuming past a line.
        let mut ch = 0;
        let len =
            std::future::poll_fn(|cx| console.poll_read(cx, std::slice::from_mut(&mut ch))).await?;
        if len == 0 {
            break;
        }

        buf.push(ch);
        if ch == b'\n' {
            break;
        }
    }

    Ok(buf)
}

/// Indicating types that can be used for `wait_for_line` matching.
pub trait MatchPattern {
    fn is_match(&self, haystack: &[u8]) -> bool;
}

impl<T: MatchPattern + ?Sized> MatchPattern for &T {
    fn is_match(&self, haystack: &[u8]) -> bool {
        T::is_match(self, haystack)
    }
}

impl MatchPattern for [u8] {
    fn is_match(&self, haystack: &[u8]) -> bool {
        memchr::memmem::find(haystack, self).is_some()
    }
}

impl MatchPattern for regex::bytes::Regex {
    fn is_match(&self, haystack: &[u8]) -> bool {
        self.is_match(haystack)
    }
}

impl MatchPattern for str {
    fn is_match(&self, haystack: &[u8]) -> bool {
        self.as_bytes().is_match(haystack)
    }
}

impl MatchPattern for regex::Regex {
    fn is_match(&self, haystack: &[u8]) -> bool {
        self.is_match(&String::from_utf8_lossy(haystack))
    }
}
