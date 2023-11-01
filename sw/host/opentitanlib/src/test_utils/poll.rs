// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Helper functions for polling in tests.
//!
//! Useful for waiting for results that may not be available immediately.

use std::cmp;
use std::thread;
use std::time::{Duration, Instant};

use anyhow::bail;

/// Poll some operation until it returns `true` or a timeout is hit.
///
/// The provided function should return `Some(x)` when the condition is met,
/// or `None` to continue polling.
///
/// `delay` can be used to prevent retrying the operation too frequently.
pub fn poll_until<F>(timeout: Duration, delay: Duration, mut f: F) -> anyhow::Result<()>
where
    F: FnMut() -> anyhow::Result<bool>,
{
    let start = Instant::now();

    loop {
        // Check if we've exceeded the timeout before trying the function.
        if start.elapsed() > timeout {
            bail!("timed out");
        }

        // Run the provided function to see if we're finished polling.
        if f()? {
            return Ok(());
        } else {
            // Delay between polls to prevent thrashing.
            let remaining = timeout.saturating_sub(start.elapsed());
            thread::sleep(cmp::min(delay, remaining));
        }
    }
}
