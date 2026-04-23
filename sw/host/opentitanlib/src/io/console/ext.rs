// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::task::{Poll, ready};
use std::time::Duration;

use anyhow::{Context, Result};

use super::ConsoleDevice;
use crate::io::console::{ConsoleError, CoverageMiddleware, Logged};

/// Extension trait to [`Uart`] where useful methods are provided.
pub trait ConsoleExt {
    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function is blocking.
    fn read(&self, buf: &mut [u8]) -> Result<usize>;

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize>;

    /// Return a wrapper that logs all outputs while reading.
    fn logged(self) -> Logged<Self>
    where
        Self: Sized;

    /// Return a wrapper that extracts coverage data.
    fn coverage(self) -> CoverageMiddleware<Self>
    where
        Self: Sized;

    /// Wait for a line that matches the specified pattern to appear.
    ///
    /// The pattern matched is returned. If timeout occurs, `None` is returned.
    fn try_wait_for_line<P: MatchPattern>(
        &self,
        pattern: P,
        timeout: Duration,
    ) -> Result<Option<P::MatchResult>>;

    /// Wait for a line that matches the specified pattern to appear.
    ///
    /// Types that can be used include:
    /// * `str`` / `[u8]`: literal matching is performed, no return value
    /// * `Regex`: regex captures are returned.
    /// * `(T, E)`, where `T` and `E` are one of the above: match two patterns at once.
    ///   If the first matches, `Ok` is returned, otherwise `Err` is. Note that when this
    ///   is used, you would have `anyhow::Result<Result<TMatch, EMatch>>` from this function,
    ///   where the `Err(_)` is I/O error or timeout, and `Ok(Err(_))` is the match for `E`.
    ///
    /// If you want to construct a static `&Regex` you can use [`regex!`] macro.
    ///
    /// [`regex!`]: crate::regex
    ///
    /// The pattern matched is returned.
    fn wait_for_line<P: MatchPattern>(
        &self,
        pattern: P,
        timeout: Duration,
    ) -> Result<P::MatchResult>;

    /// Wait on the console until the coverage profile end or skip anchor is received.
    fn wait_for_coverage(&self, timeout: Duration) -> Result<()>;
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

    fn logged(self) -> Logged<Self>
    where
        Self: Sized,
    {
        Logged::new(self)
    }

    fn coverage(self) -> CoverageMiddleware<Self>
    where
        Self: Sized,
    {
        CoverageMiddleware::new(self)
    }

    fn try_wait_for_line<P: MatchPattern>(
        &self,
        pattern: P,
        timeout: Duration,
    ) -> Result<Option<P::MatchResult>> {
        crate::util::runtime::block_on(async {
            match tokio::time::timeout(timeout, async {
                loop {
                    let line = read_line(self).await?;
                    if let Some(m) = pattern.perform_match(&line) {
                        return Ok(m);
                    }
                }
            })
            .await
            {
                Ok(Ok(v)) => Ok(Some(v)),
                Ok(Err(e)) => Err(e),
                Err(_) => Ok(None),
            }
        })
    }

    fn wait_for_line<P: MatchPattern>(
        &self,
        pattern: P,
        timeout: Duration,
    ) -> Result<P::MatchResult> {
        self.try_wait_for_line(pattern, timeout)?
            .with_context(|| ConsoleError::TimedOut)
    }

    fn wait_for_coverage(&self, timeout: Duration) -> Result<()> {
        let coverage = self.as_coverage_console().ok_or_else(|| {
            ConsoleError::GenericError("Coverage extraction not supported by this device".into())
        })?;
        let initial = coverage.coverage_blocks_processed();
        crate::util::runtime::block_on(async {
            tokio::time::timeout(timeout, async {
                std::future::poll_fn(|cx| {
                    if coverage.coverage_blocks_processed() > initial {
                        return Poll::Ready(Ok(()));
                    }
                    let mut buf = [0u8; 1024];
                    match ready!(self.poll_read(cx, &mut buf)) {
                        Ok(0) => Poll::Ready(Err(ConsoleError::GenericError(
                            "EOF reached while waiting for coverage".into(),
                        )
                        .into())),
                        Ok(_) => {
                            cx.waker().wake_by_ref();
                            Poll::Pending
                        }
                        Err(e) => Poll::Ready(Err(e)),
                    }
                })
                .await
            })
            .await
            .context("Timed out waiting for coverage")?
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
    type MatchResult;

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult>;
}

impl<T: MatchPattern + ?Sized> MatchPattern for &T {
    type MatchResult = T::MatchResult;

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult> {
        T::perform_match(self, haystack)
    }
}

impl MatchPattern for [u8] {
    type MatchResult = ();

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult> {
        memchr::memmem::find(haystack, self).map(|_| ())
    }
}

impl MatchPattern for regex::bytes::Regex {
    type MatchResult = Vec<Vec<u8>>;

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult> {
        Some(
            self.captures(haystack)?
                .iter()
                .map(|x| x.map(|m| m.as_bytes().to_owned()).unwrap_or_default())
                .collect(),
        )
    }
}

impl MatchPattern for str {
    type MatchResult = ();

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult> {
        self.as_bytes().perform_match(haystack)
    }
}

impl MatchPattern for regex::Regex {
    type MatchResult = Vec<String>;

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult> {
        let haystack = String::from_utf8_lossy(haystack);
        Some(
            self.captures(&haystack)?
                .iter()
                .map(|x| x.map(|m| m.as_str().to_owned()).unwrap_or_default())
                .collect(),
        )
    }
}

/// Match two patterns at once.
pub struct PassFail<T, E>(pub T, pub E);

pub enum PassFailResult<T, E> {
    Pass(T),
    Fail(E),
}

impl<T: MatchPattern, E: MatchPattern> MatchPattern for PassFail<T, E> {
    type MatchResult = PassFailResult<T::MatchResult, E::MatchResult>;

    fn perform_match(&self, haystack: &[u8]) -> Option<Self::MatchResult> {
        if let Some(m) = self.1.perform_match(haystack) {
            return Some(PassFailResult::Fail(m));
        }

        Some(PassFailResult::Pass(self.0.perform_match(haystack)?))
    }
}
