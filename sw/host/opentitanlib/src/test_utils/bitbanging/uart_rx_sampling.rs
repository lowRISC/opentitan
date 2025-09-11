// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::iter::Peekable;
use std::time::Duration;
use std::vec::Vec;

use anyhow::{Result, bail};
use thiserror::Error;

use crate::io::gpio::{
    ClockNature, Edge, MonitoringEvent, MonitoringReadResponse, MonitoringStartResponse,
};
use crate::test_utils::bitbanging::uart::{UartBitbangDecoder, UartTransfer};

#[derive(Error, Debug, PartialEq)]
pub enum UartBitbangError {
    #[error("Uart bitbanging RX monitoring needs a more reliable clock source")]
    InaccurateMonitoringClock,
    #[error("RX monitoring recorded double rising edge")]
    DoubleRisingEdge,
    #[error("RX monitoring recorded double falling edge")]
    DoubleFallingEdge,
    #[error("RX monitoring provided edges out-of-order")]
    EdgesOutOfOrder,
}

/// A wrapper for the `UartBitbangDecoder` which converts the waveform returned
/// by the `GpioMonitoring` interface into the uniform discrete samples that
/// are understood by the decoder. This performs uniform sampling according to
/// the baud rate from the initial response and the edges provided by monitor
/// reads, optimized to avoid sampling whilst the UART is idle.
pub struct UartRxMonitoringDecoder<const RX: u8> {
    pub decoder: UartBitbangDecoder<RX>,
    clock_resolution: u64,
    initial_timestamp: u64,
    last_event: Option<MonitoringEvent>,
    next_sample_time: Option<u64>,
}

impl<const RX: u8> UartRxMonitoringDecoder<RX> {
    pub fn new(
        decoder: UartBitbangDecoder<RX>,
        clock_nature: ClockNature,
        start: MonitoringStartResponse,
    ) -> Result<Self> {
        let ClockNature::Wallclock { resolution, .. } = clock_nature else {
            bail!(UartBitbangError::InaccurateMonitoringClock);
        };
        Ok(Self {
            decoder,
            clock_resolution: resolution,
            initial_timestamp: start.timestamp,
            last_event: None,
            next_sample_time: None,
        })
    }

    /// Convert a `u64` timestamp to a time in nanoseconds based on the initial
    /// monitoring offset timestamp and configured clock resolution.
    fn timestamp_to_nanos(&self, timestamp: u64) -> u64 {
        let delta = (timestamp - self.initial_timestamp) as u128;
        let nanos = delta * 1_000_000_000u128 / self.clock_resolution as u128;
        nanos as u64
    }

    /// Calculates the number of samples between two timestamps, assuming a
    /// sample was taken at the given `from` time.
    fn samples_since(&self, from: u64, until: u64, period_ns: u64) -> u64 {
        let time_elapsed = until - from;
        time_elapsed / period_ns
    }

    /// Consume edge events until several identical samples are found between
    /// edges. Lets us to wait for a break condition / idle even if monitoring
    /// starts mid-transmission. Returns `true` if in a stable state.
    fn sample_until_stable_state<I: Iterator<Item = MonitoringEvent>>(
        &mut self,
        events: &mut Peekable<I>,
        end_time: u64,
        period_ns: u64,
    ) -> Result<bool> {
        let frame_bit_time = self.decoder.config.bit_time_per_frame() as u64;
        let last_ts = if let Some(last_event) = self.last_event {
            last_event.timestamp
        } else {
            self.initial_timestamp
        };
        let mut last_time = self.timestamp_to_nanos(last_ts);

        while let Some(event) = events.peek() {
            if event.signal_index != RX {
                events.next();
                continue;
            }
            let timestamp = self.timestamp_to_nanos(event.timestamp);
            if timestamp < last_time {
                bail!(UartBitbangError::EdgesOutOfOrder)
            } else if self.samples_since(last_time, timestamp, period_ns) > frame_bit_time {
                return Ok(true);
            }
            last_time = timestamp;
            self.last_event = events.next();
        }
        Ok(self.samples_since(last_time, end_time, period_ns) > frame_bit_time)
    }

    /// Without consuming any events, find the previous sample time and RX
    /// value stored by the decoder. If no sampling has been performed
    /// previously, synchronize with the initial falling edge.
    fn get_last_state<I: Iterator<Item = MonitoringEvent>>(
        &mut self,
        events: &mut Peekable<I>,
        end_time: u64,
        period_ns: u64,
    ) -> Result<Option<(u64, u8)>> {
        // If we have information stored from a previous sample, retrieve it.
        if let Some(next_sample_time) = self.next_sample_time {
            let Some(last_event) = self.last_event else {
                bail!("Previous sampling time exists but previous event does not");
            };
            let value = match last_event.edge {
                Edge::Rising => 0x01,
                Edge::Falling => 0x00,
            };
            return Ok(Some((next_sample_time, value)));
        };

        // No previous sampling, so wait for a stable RX level to avoid desync
        if !self.sample_until_stable_state(events, end_time, period_ns)? {
            return Ok(None);
        }

        // Identify & synchronize with the first falling edge
        let Some(mut first_event) = events.peek() else {
            return Ok(None);
        };
        while first_event.signal_index != RX {
            events.next();
            let Some(event) = events.peek() else {
                return Ok(None);
            };
            first_event = event;
        }

        let edge_time = if first_event.edge == Edge::Falling {
            self.timestamp_to_nanos(first_event.timestamp)
        } else {
            events.next();
            let Some(second_event) = events.peek() else {
                return Ok(None);
            };
            self.timestamp_to_nanos(second_event.timestamp)
        };
        let next_sample_time = edge_time + period_ns / 2;
        Ok(Some((next_sample_time, 0x01)))
    }

    /// Uses the bitbanging decoder to decode a given RX pin sample.
    fn decode_sample(&mut self, sample: u8, decoded: &mut Vec<u8>) -> Result<()> {
        if let Some(transfer) = self.decoder.decode_sample(sample)? {
            match transfer {
                UartTransfer::Byte { data } => decoded.push(data),
                UartTransfer::Broken { error, .. } => {
                    bail!(error)
                }
                // TODO: handle decoding incoming break conditions
                UartTransfer::Break => (),
            }
        }
        Ok(())
    }

    /// Decode a given RX monitoring waveform edge, calculating & decoding
    /// uniform RX pin samples between this edge and the previous one.
    fn decode_edge(
        &mut self,
        event: MonitoringEvent,
        decoded: &mut Vec<u8>,
        period_ns: u64,
        next_sample_time: &mut u64,
        value: &mut u8,
    ) -> Result<()> {
        if event.edge == Edge::Falling && *value == 0 {
            bail!(UartBitbangError::DoubleFallingEdge);
        } else if event.edge == Edge::Rising && *value == 1 {
            bail!(UartBitbangError::DoubleRisingEdge);
        }
        let sampling_end = self.timestamp_to_nanos(event.timestamp) + period_ns;
        if sampling_end < *next_sample_time {
            bail!(UartBitbangError::EdgesOutOfOrder)
        }

        // Calculate & decode samples between edges
        let num_samples = self.samples_since(*next_sample_time, sampling_end, period_ns);
        *next_sample_time += period_ns * num_samples;
        for _ in 0..num_samples {
            if self.decoder.is_idle() && event.edge == Edge::Falling {
                // Optimization: don't decode idle-high samples between frames
                break;
            }
            self.decode_sample(*value << RX, decoded)?;
        }

        if self.decoder.is_idle() && event.edge == Edge::Falling {
            // Reset sampling time at the start of each transaction
            *next_sample_time = self.timestamp_to_nanos(event.timestamp) + period_ns / 2;
        }
        self.last_event = Some(event);
        *value = if *value == 0x00 { 0x01 } else { 0x00 };
        Ok(())
    }

    /// Decode a given RX monitoring waveform  into received bytes, where the
    /// waveform is an ordered vector of RX edges, and the time at which the
    /// monitoring was performed (i.e. the end).
    fn decode_waveform(
        &mut self,
        events: Vec<MonitoringEvent>,
        end_time: u64,
        period: &Duration,
    ) -> Result<Vec<u8>> {
        let mut decoded = Vec::new();
        let mut events_iter = events.into_iter().peekable();
        let period_ns = period.as_nanos() as u64;
        let last_state = self.get_last_state(&mut events_iter, end_time, period_ns)?;
        let Some((mut next_sample_time, mut value)) = last_state else {
            // Not enough events recorded to find a starting state.
            return Ok(decoded);
        };
        for event in events_iter {
            if event.signal_index != RX {
                continue;
            }
            self.decode_edge(
                event,
                &mut decoded,
                period_ns,
                &mut next_sample_time,
                &mut value,
            )?;
        }
        self.next_sample_time = Some(next_sample_time);
        // When a frame finishes, a final rising edge leaves the RX line high,
        // but our sampling mechanism only decodes samples between edges. To
        // avoid requiring subsequent transmissions, add idle bits until the
        // read timestamp (while the decoder is active).
        if value != 0x00 {
            while !self.decoder.is_idle() {
                next_sample_time += period_ns;
                if next_sample_time >= end_time {
                    break;
                }
                self.next_sample_time = Some(next_sample_time);
                self.decode_sample(value << RX, &mut decoded)?;
            }
        }
        Ok(decoded)
    }

    /// Decode a `MonitoringReadResponse` from the `GpioMonitoring` interface,
    /// performing uniform sampling and decoding the sampled UART output.
    ///
    /// Note: it is expected that *all* monitor responses since monitoring
    /// initialization are fed to the decoder through this function. If any
    /// monitoring events are lost, this could cause the corruption of some
    /// received UART data.
    pub fn decode_response(
        &mut self,
        response: MonitoringReadResponse,
        baud_rate: u32,
    ) -> Result<Vec<u8>> {
        let sampling_period = Duration::from_nanos(1_000_000_000u64 / baud_rate as u64);
        let read_timestamp = self.timestamp_to_nanos(response.timestamp);
        self.decode_waveform(response.events, read_timestamp, &sampling_period)
    }
}
