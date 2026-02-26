// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::VecDeque;
use std::fs;
use std::sync::Mutex;
use std::task::{Context, Poll, ready};

use anyhow::{Result, bail};
use crc::{CRC_32_ISO_HDLC, Crc};

use super::{ConsoleDevice, CoverageConsole};
use crate::io::middleware::{Middleware, UartMiddleware};
use crate::io::uart::Uart;

const COVERAGE_START_ANCHOR: &[u8] = b"== COVERAGE PROFILE START ==\r\n";
const COVERAGE_END_ANCHOR: &[u8] = b"== COVERAGE PROFILE END ==\r\n";
const COVERAGE_SKIP_ANCHOR: &[u8] = b"== COVERAGE PROFILE SKIP ==\r\n";

#[derive(Default, PartialEq, Clone, Copy)]
enum BufferMode {
    #[default]
    Normal,
    Coverage,
}

pub struct CoverageMiddleware<T> {
    inner: T,
    profile_path_template: Option<String>,
    state: Mutex<CoverageState>,
}

struct CoverageState {
    mode: BufferMode,
    /// Buffer for matching anchors.
    match_buf: VecDeque<u8>,
    /// Buffer for confirmed normal data ready to be returned to the user.
    output_buf: VecDeque<u8>,
    /// Buffer for coverage data (hex encoded).
    coverage_buf: String,
    /// Number of coverage blocks processed (finished or skipped).
    blocks_processed: usize,
}

impl<T> CoverageMiddleware<T> {
    pub fn new(inner: T) -> Self {
        Self {
            inner,
            profile_path_template: None,
            state: Mutex::new(CoverageState {
                mode: BufferMode::Normal,
                match_buf: VecDeque::new(),
                output_buf: VecDeque::new(),
                coverage_buf: String::new(),
                blocks_processed: 0,
            }),
        }
    }

    #[cfg(test)]
    pub fn new_with_template(inner: T, template: String) -> Self {
        Self {
            inner,
            profile_path_template: Some(template),
            state: Mutex::new(CoverageState {
                mode: BufferMode::Normal,
                match_buf: VecDeque::new(),
                output_buf: VecDeque::new(),
                coverage_buf: String::new(),
                blocks_processed: 0,
            }),
        }
    }

    fn starts_with_any_anchor(data: &[u8]) -> Option<&'static [u8]> {
        if data.starts_with(COVERAGE_START_ANCHOR) {
            return Some(COVERAGE_START_ANCHOR);
        }
        if data.starts_with(COVERAGE_END_ANCHOR) {
            return Some(COVERAGE_END_ANCHOR);
        }
        if data.starts_with(COVERAGE_SKIP_ANCHOR) {
            return Some(COVERAGE_SKIP_ANCHOR);
        }
        None
    }

    fn is_any_anchor_prefix(data: &[u8]) -> bool {
        !data.is_empty()
            && (COVERAGE_START_ANCHOR.starts_with(data)
                || COVERAGE_END_ANCHOR.starts_with(data)
                || COVERAGE_SKIP_ANCHOR.starts_with(data))
    }

    fn process_coverage_data(&self, coverage_buf: &str) -> Result<()> {
        let response = hex::decode(coverage_buf)?;
        if response.len() < 4 {
            bail!(
                "Coverage from the device is too short: {} bytes",
                response.len()
            );
        }

        let (response, crc) = response.split_at(response.len() - 4);
        let crc = u32::from_le_bytes(crc.try_into()?);
        let actual = Crc::<u32>::new(&CRC_32_ISO_HDLC).checksum(response);
        if crc != actual {
            bail!("Coverage corrupted: crc = {crc:08x}, actual = {actual:08x}");
        }

        let template = self
            .profile_path_template
            .clone()
            .or_else(|| std::env::var("LLVM_PROFILE_FILE").ok())
            .unwrap_or_else(|| "./default.%p.profraw".to_owned());

        let path = template.replace("%h", "test.on.device");
        let path = path.replace("%p", &rand::random::<u32>().to_string());
        let path = path.replace("%m", "0");
        let path = path.replace(".profraw", ".xprofraw");

        log::info!("Saving coverage profile to {}", path);
        fs::write(path, response)?;

        Ok(())
    }
}

impl<T: ConsoleDevice> Middleware for CoverageMiddleware<T> {
    type Inner = T;
    fn inner(&self) -> &T {
        &self.inner
    }
}

impl<T: Uart> UartMiddleware for CoverageMiddleware<T> {
    fn clear_rx_buffer_impl(&self) -> Result<()> {
        let mut state = self.state.lock().unwrap();
        state.mode = BufferMode::Normal;
        state.match_buf.clear();
        state.output_buf.clear();
        state.coverage_buf.clear();
        state.blocks_processed = 0;
        self.inner.clear_rx_buffer()
    }
}

impl<T: ConsoleDevice> ConsoleDevice for CoverageMiddleware<T> {
    fn poll_read(&self, cx: &mut Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        // If the inner device already supports coverage, this middleware is a no-op.
        if self.inner.as_coverage_console().is_some() {
            return self.inner.poll_read(cx, buf);
        }

        if buf.is_empty() {
            return Poll::Ready(Ok(0));
        }
        let mut state = self.state.lock().unwrap();

        loop {
            // First, satisfy from output_buf if possible.
            if !state.output_buf.is_empty() {
                let len = std::cmp::min(buf.len(), state.output_buf.len());
                for b in buf.iter_mut().take(len) {
                    *b = state.output_buf.pop_front().unwrap();
                }
                return Poll::Ready(Ok(len));
            }

            // output_buf is empty, try to move data from match_buf.
            if !state.match_buf.is_empty() {
                let mode = state.mode;
                let match_buf_flat = state.match_buf.make_contiguous();

                if let Some(anchor) = Self::starts_with_any_anchor(match_buf_flat) {
                    for _ in 0..anchor.len() {
                        state.match_buf.pop_front();
                    }
                    if mode == BufferMode::Normal {
                        if anchor == COVERAGE_START_ANCHOR {
                            state.mode = BufferMode::Coverage;
                            state.coverage_buf.clear();
                        } else if anchor == COVERAGE_END_ANCHOR {
                            log::warn!("Got unexpected coverage end indicator!");
                            state.blocks_processed += 1;
                            cx.waker().wake_by_ref();
                            return Poll::Pending;
                        } else if anchor == COVERAGE_SKIP_ANCHOR {
                            state.blocks_processed += 1;
                            cx.waker().wake_by_ref();
                            return Poll::Pending;
                        }
                    } else {
                        // Coverage mode
                        if anchor == COVERAGE_START_ANCHOR {
                            log::warn!("Got unterminated coverage block:\n{}", state.coverage_buf);
                            state.coverage_buf.clear();
                        } else if anchor == COVERAGE_END_ANCHOR {
                            if let Err(e) = self.process_coverage_data(&state.coverage_buf) {
                                log::warn!("Failed to process coverage data: {:?}", e);
                            }
                            state.mode = BufferMode::Normal;
                            state.coverage_buf.clear();
                            state.blocks_processed += 1;
                            cx.waker().wake_by_ref();
                            return Poll::Pending;
                        } else if anchor == COVERAGE_SKIP_ANCHOR {
                            log::warn!("Got unterminated coverage block:\n{}", state.coverage_buf);
                            state.mode = BufferMode::Normal;
                            state.coverage_buf.clear();
                            state.blocks_processed += 1;
                            cx.waker().wake_by_ref();
                            return Poll::Pending;
                        }
                    }
                    continue;
                }

                // Not starting with an anchor. Find safe portion of match_buf.
                let mut safe_len = 0;
                while safe_len < match_buf_flat.len() {
                    if Self::is_any_anchor_prefix(&match_buf_flat[safe_len..]) {
                        break;
                    }
                    safe_len += 1;
                }

                if safe_len > 0 {
                    if mode == BufferMode::Normal {
                        for _ in 0..safe_len {
                            let ch = state.match_buf.pop_front().unwrap();
                            state.output_buf.push_back(ch);
                        }
                        // Loop to return from output_buf.
                        continue;
                    } else {
                        for _ in 0..safe_len {
                            let ch_byte = state.match_buf.pop_front().unwrap();
                            if ch_byte.is_ascii_hexdigit() {
                                state.coverage_buf.push(ch_byte as char);
                            } else {
                                log::warn!(
                                    "Got invalid hex character '{}' in coverage block. Exiting coverage mode.",
                                    (ch_byte as char).escape_default()
                                );
                                state.mode = BufferMode::Normal;
                                state.coverage_buf.clear();
                                state.output_buf.push_back(ch_byte);
                                state.blocks_processed += 1;
                                cx.waker().wake_by_ref();
                                return Poll::Pending;
                            }
                        }
                        continue;
                    }
                }
                // match_buf starts with a prefix, must wait for more data.
            }

            // Need more data from inner. Read 1 byte.
            let mut one_byte = [0u8; 1];
            drop(state);
            let res = ready!(self.inner.poll_read(cx, &mut one_byte));
            state = self.state.lock().unwrap();

            match res {
                Ok(0) => {
                    // EOF. Flush match_buf.
                    if !state.match_buf.is_empty() {
                        if state.mode == BufferMode::Normal {
                            while let Some(ch) = state.match_buf.pop_front() {
                                state.output_buf.push_back(ch);
                            }
                            continue;
                        } else {
                            log::warn!("EOF reached with unterminated coverage block");
                            while let Some(ch) = state.match_buf.pop_front() {
                                let ch = ch as char;
                                state.coverage_buf.push(ch);
                            }
                            return Poll::Ready(Ok(0));
                        }
                    }
                    return Poll::Ready(Ok(0));
                }
                Ok(1) => {
                    state.match_buf.push_back(one_byte[0]);
                }
                _ => unreachable!(),
            }
        }
    }

    fn write(&self, buf: &[u8]) -> Result<()> {
        self.inner.write(buf)
    }

    fn as_coverage_console(&self) -> Option<&dyn CoverageConsole> {
        self.inner.as_coverage_console().or(Some(self))
    }
}

impl<T: ConsoleDevice> CoverageConsole for CoverageMiddleware<T> {
    fn coverage_blocks_processed(&self) -> usize {
        self.state.lock().unwrap().blocks_processed
    }
}
