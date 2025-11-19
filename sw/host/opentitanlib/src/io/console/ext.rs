// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use anyhow::Result;

use super::ConsoleDevice;

/// Extension trait to [`Uart`] where useful methods are provided.
pub trait ConsoleExt {
    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function is blocking.
    fn read(&self, buf: &mut [u8]) -> Result<usize>;

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize>;
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
}
