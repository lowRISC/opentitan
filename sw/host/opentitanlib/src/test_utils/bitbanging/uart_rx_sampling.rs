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
pub struct UartRxMonitoringDecoder {
    pub decoder: UartBitbangDecoder,
    clock_resolution: u64,
    initial_timestamp: u64,
    last_event: Option<MonitoringEvent>,
    last_sample_time: Option<u64>,
}

impl UartRxMonitoringDecoder {
    pub fn new(
        decoder: UartBitbangDecoder,
        clock_nature: ClockNature,
        start: MonitoringStartResponse,
    ) -> Result<Self> {
        let ClockNature::Wallclock { resolution, .. } = clock_nature else {
            Err(UartBitbangError::InaccurateMonitoringClock)?
        };
        Ok(Self {
            decoder,
            clock_resolution: resolution,
            initial_timestamp: start.timestamp,
            last_event: None,
            last_sample_time: None,
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
        // Rounding division of time_elapsed / period_ns
        (time_elapsed + period_ns / 2) / period_ns
    }

    /// Consume edge events until several identical samples are found between
    /// edges. Lets us wait for a break condition / idle event if monitoring
    /// starts mid-transmission. Returns `true` if in a stable state.
    fn sample_until_stable_state<I: Iterator<Item = MonitoringEvent>>(
        &mut self,
        events: &mut Peekable<I>,
        end_time: u64,
        period_ns: u64,
    ) -> Result<bool> {
        let frame_bit_time = self.decoder.config.bit_time_per_frame() as u64;
        let last_ts = match self.last_event {
            Some(last_event) => last_event.timestamp,
            None => self.initial_timestamp,
        };
        let mut last_time = self.timestamp_to_nanos(last_ts);

        while let Some(event) = events.peek() {
            let timestamp = self.timestamp_to_nanos(event.timestamp);
            if timestamp < last_time {
                Err(UartBitbangError::EdgesOutOfOrder)?
            } else if self.samples_since(last_time, timestamp, period_ns) > frame_bit_time {
                return Ok(true);
            }
            last_time = timestamp;
            self.last_event = events.next();
        }
        Ok(self.samples_since(last_time, end_time, period_ns) > frame_bit_time)
    }

    /// Find the previous sample time and RX value stored by the decoder. If no
    /// sampling has been performed previously, wait for a stable RX level
    /// (no edges for >= UART frame time) and then synchronize with the initial
    /// falling edge.
    ///
    /// This will consume edge events until a stable state is found, but will
    /// not consume the event corresponding to the first falling edge.
    fn get_last_state<I: Iterator<Item = MonitoringEvent>>(
        &mut self,
        events: &mut Peekable<I>,
        end_time: u64,
        period_ns: u64,
    ) -> Result<Option<(u64, u8)>> {
        // If we have information stored from a previous sample, retrieve it.
        if let Some(last_sample_time) = self.last_sample_time {
            let Some(last_event) = self.last_event else {
                bail!("Previous sampling time exists but previous event does not");
            };
            let value = match last_event.edge {
                Edge::Rising => 0x01,
                Edge::Falling => 0x00,
            };
            return Ok(Some((last_sample_time, value)));
        };

        // No previous sampling, so wait for a stable RX level to avoid desync
        if !self.sample_until_stable_state(events, end_time, period_ns)? {
            return Ok(None);
        }

        // Identify & synchronize with the first falling edge
        let Some(first_event) = events.peek() else {
            return Ok(None);
        };

        let edge_time = if first_event.edge == Edge::Falling {
            self.timestamp_to_nanos(first_event.timestamp)
        } else {
            // If we start in a break condition, wait until the break is clear
            // (the UART goes idle) and sync with the next (falling) edge.
            events.next();
            let Some(second_event) = events.peek() else {
                return Ok(None);
            };
            self.timestamp_to_nanos(second_event.timestamp)
        };
        Ok(Some((edge_time, 0x01)))
    }

    /// Uses the bitbanging decoder to decode a given RX pin sample.
    fn decode_sample(&mut self, sample: u8, decoded: &mut Vec<u8>) -> Result<()> {
        if let Some(transfer) = self.decoder.decode_sample(sample)? {
            match transfer {
                UartTransfer::Byte { data } => decoded.push(data),
                UartTransfer::Broken { error, .. } => {
                    Err(error)?;
                }
                // TODO: handle decoding incoming break conditions
                UartTransfer::Break => (),
            }
        }
        Ok(())
    }

    /// Decode a given RX monitoring waveform edge, calculating & decoding
    /// uniform RX pin samples between this edge and the previous one.
    ///
    /// Args:
    /// - event: The `MonitoringEvent` representing an edge to decode.
    /// - decoded: The `Vec` to place decoded UART characters into.
    /// - period_ns: The sampling period in nanos (according to the Baud rate).
    /// - last_sample_time: The timestamp (in nanoseconds) at which the
    ///   previous edge/sample occurred. A sample (or several samples) will be
    ///   taken if the edge occurs more than 1/2 a period after this time, and
    ///   the time will then be correspondingly updated.
    /// - value: The current value of the UART RX signal. Will be updated from
    ///   the given edge.
    fn decode_edge(
        &mut self,
        event: MonitoringEvent,
        decoded: &mut Vec<u8>,
        period_ns: u64,
        last_sample_time: &mut u64,
        value: &mut u8,
    ) -> Result<()> {
        if event.edge == Edge::Falling && *value == 0 {
            Err(UartBitbangError::DoubleFallingEdge)?
        } else if event.edge == Edge::Rising && *value == 1 {
            Err(UartBitbangError::DoubleRisingEdge)?
        }
        let sampling_end = self.timestamp_to_nanos(event.timestamp);
        if sampling_end < *last_sample_time {
            Err(UartBitbangError::EdgesOutOfOrder)?
        }

        // Calculate & decode samples between edges
        let num_samples = self.samples_since(*last_sample_time, sampling_end, period_ns);
        *last_sample_time += period_ns * num_samples;
        for _ in 0..num_samples {
            if self.decoder.is_idle() && event.edge == Edge::Falling {
                // Optimization: don't decode idle-high samples between frames
                break;
            }
            self.decode_sample(*value, decoded)?;
        }

        if self.decoder.is_idle() && event.edge == Edge::Falling {
            // Reset sampling time at the start of each transaction
            *last_sample_time = self.timestamp_to_nanos(event.timestamp);
        }
        self.last_event = Some(event);
        *value = if *value == 0x00 { 0x01 } else { 0x00 };
        Ok(())
    }

    /// Decode a given RX monitoring waveform  into received bytes, where the
    /// waveform is an ordered vector of RX edges, and the time at which the
    /// monitoring was performed (i.e. the end).
    ///
    /// Args:
    /// - events: The list of `MonitoringEvents` in the response waveform.
    /// - signal_index: The index of the RX signal in the monitoring events.
    /// - end_time: The final timestamp of the response waveform.
    /// - period: The period at which to sample (according to the Baud rate).
    fn decode_waveform(
        &mut self,
        events: Vec<MonitoringEvent>,
        signal_index: u8,
        end_time: u64,
        period: &Duration,
    ) -> Result<Vec<u8>> {
        let mut decoded = Vec::new();
        let mut events_iter = events
            .into_iter()
            .filter(|event| event.signal_index == signal_index)
            .peekable();
        let period_ns = period.as_nanos() as u64;
        let last_state = self.get_last_state(&mut events_iter, end_time, period_ns)?;
        let Some((mut last_sample_time, mut value)) = last_state else {
            // Not enough events recorded to find a starting state.
            return Ok(decoded);
        };
        for event in events_iter {
            self.decode_edge(
                event,
                &mut decoded,
                period_ns,
                &mut last_sample_time,
                &mut value,
            )?;
        }
        self.last_sample_time = Some(last_sample_time);
        // When a frame finishes, a final rising edge leaves the RX line high,
        // but our sampling mechanism only decodes samples between edges. To
        // avoid requiring subsequent transmissions, add idle bits until the
        // read timestamp (while the decoder is active).
        if value != 0x00 {
            while !self.decoder.is_idle() {
                if (last_sample_time + period_ns / 2) >= end_time {
                    break;
                }
                last_sample_time += period_ns;
                self.last_sample_time = Some(last_sample_time);
                self.decode_sample(value, &mut decoded)?;
            }
        }
        Ok(decoded)
    }

    /// Decode a `MonitoringReadResponse` from the `GpioMonitoring` interface,
    /// performing uniform sampling and decoding the sampled UART output.
    /// `signal_index` specifies the `MonitoringReadResponse` signal
    /// corresponding to the UART RX pin (normally 0).
    ///
    /// Expects at least a UART frame time of idle since the initial timestamp
    /// before it will start sampling (any malformed data is dropped).
    ///
    /// Note: it is expected that *all* monitor responses since monitoring
    /// initialization are fed to the decoder through this function. If any
    /// monitoring events are lost, this could cause the corruption of some
    /// received UART data.
    pub fn decode_response(
        &mut self,
        response: MonitoringReadResponse,
        signal_index: u8,
        baud_rate: u32,
    ) -> Result<Vec<u8>> {
        let sampling_period = Duration::from_nanos(1_000_000_000u64 / baud_rate as u64);
        let read_end_timestamp = self.timestamp_to_nanos(response.timestamp);
        self.decode_waveform(
            response.events,
            signal_index,
            read_end_timestamp,
            &sampling_period,
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::sync::LazyLock;

    use serialport::Parity;

    use crate::test_utils::bitbanging::uart::{UartBitbangConfig, UartStopBits};

    static CLOCK_NATURE: ClockNature = ClockNature::Wallclock {
        resolution: 1_000_000,
        offset: None,
    };
    static BAUD_RATE: u32 = 57600;
    static START_RESPONSE: LazyLock<MonitoringStartResponse> =
        LazyLock::new(|| MonitoringStartResponse {
            timestamp: 0,
            initial_levels: vec![true],
        });
    // Example UART RX waveform taken from a bitbanging test sample
    static EVENT_TIMESTAMPS: [u64; 112] = [
        5889252340, 5889252358, 5889252375, 5889252392, 5889252410, 5889252427, 5889252445,
        5889252462, 5889252479, 5889252497, 5889252514, 5889252532, 5889252549, 5889252636,
        5889252654, 5889252671, 5889252688, 5889252723, 5889252740, 5889252775, 5889252793,
        5889252810, 5889252827, 5889252845, 5889252862, 5889252914, 5889252932, 5889252949,
        5889252967, 5889252984, 5889253001, 5889253019, 5889253036, 5889253141, 5889253158,
        5889253193, 5889253210, 5889253245, 5889253263, 5889253315, 5889253349, 5889253367,
        5889253386, 5889253402, 5889253419, 5889253454, 5889253471, 5889253489, 5889253523,
        5889253541, 5889253558, 5889253610, 5889253628, 5889253645, 5889253697, 5889253715,
        5889253732, 5889253767, 5889253784, 5889253837, 5889253871, 5889253889, 5889253906,
        5889253924, 5889253941, 5889254011, 5889254046, 5889254063, 5889254080, 5889254115,
        5889254167, 5889254185, 5889254219, 5889254238, 5889254254, 5889254272, 5889254324,
        5889254359, 5889254393, 5889254411, 5889254428, 5889254533, 5889254550, 5889254585,
        5889254603, 5889254655, 5889254672, 5889254689, 5889254741, 5889254759, 5889254776,
        5889254794, 5889254811, 5889254828, 5889254846, 5889254881, 5889254915, 5889254933,
        5889254950, 5889254968, 5889255002, 5889255037, 5889255089, 5889255107, 5889255124,
        5889255176, 5889255194, 5889255211, 5889255264, 5889255281, 5889255298, 5889255455,
    ];
    static READ_RESPONSE_TIMESTAMP: u64 = 5889262827;
    static EXPECTED_RESPONSE: &str = "UART bitbang test\0";

    // A helper to compactly construct `MonitoringEvent` edges.
    fn edge(signal_index: u8, edge: Edge, timestamp: u64) -> MonitoringEvent {
        MonitoringEvent {
            signal_index,
            edge,
            timestamp,
        }
    }

    fn sample_and_decode(
        decoder: UartBitbangDecoder,
        start_idle: bool,
        start_response: MonitoringStartResponse,
        edge_timestamps: &[u64],
        read_timestamp: u64,
        baud_rate: u32,
        expected: String,
    ) -> Result<()> {
        let edges = if start_idle {
            [Edge::Falling, Edge::Rising]
        } else {
            [Edge::Rising, Edge::Falling]
        };
        let events = edge_timestamps
            .iter()
            .enumerate()
            .map(|(i, t)| edge(0, edges[i % 2], *t))
            .collect::<Vec<_>>();
        let read_response = MonitoringReadResponse {
            events,
            timestamp: read_timestamp,
        };

        let mut response_decoder =
            UartRxMonitoringDecoder::new(decoder, CLOCK_NATURE, start_response)?;
        let decoded = response_decoder.decode_response(read_response, 0, baud_rate)?;
        assert_eq!(String::from_utf8(decoded), Ok(expected));
        Ok(())
    }

    #[test]
    fn smoke() -> Result<()> {
        // Decode against a known sample test string
        let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
        let decoder = UartBitbangDecoder::new(config);
        sample_and_decode(
            decoder,
            true,
            START_RESPONSE.clone(),
            &EVENT_TIMESTAMPS,
            READ_RESPONSE_TIMESTAMP,
            BAUD_RATE,
            EXPECTED_RESPONSE.into(),
        )
    }

    #[test]
    fn baud_rates() -> Result<()> {
        // Check we can sample at different baud rates
        fn modify_timestamp(timestamp: u64, first_edge_timestamp: u64, divider: u32) -> u64 {
            let delta = timestamp - first_edge_timestamp;
            let new_delta = delta * divider as u64;
            first_edge_timestamp + new_delta
        }

        let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
        let first_edge_timestamp = EVENT_TIMESTAMPS[0];
        for divider in 1..=10u32 {
            let modified_timestamps = EVENT_TIMESTAMPS
                .iter()
                .map(|timestamp| modify_timestamp(*timestamp, first_edge_timestamp, divider))
                .collect::<Vec<_>>();
            let modified_baud = BAUD_RATE / divider;
            let modified_response_timestamp =
                modify_timestamp(READ_RESPONSE_TIMESTAMP, first_edge_timestamp, divider);
            let decoder = UartBitbangDecoder::new(config.clone());
            sample_and_decode(
                decoder,
                true,
                START_RESPONSE.clone(),
                &modified_timestamps,
                modified_response_timestamp,
                modified_baud,
                EXPECTED_RESPONSE.into(),
            )?;
        }
        Ok(())
    }

    #[test]
    fn clock_jitter_and_skew() -> Result<()> {
        // Check we can tolerate some small +-5% jitters or skews
        // Use a smaller baud rate to allow more accurate jitters
        const BAUD_DIVIDER: u32 = 8;

        fn modify_timestamp(
            timestamp: u64,
            first_edge_timestamp: u64,
            period_ns: u64,
            skew_pc: i32,
            jitter_pc: i32,
        ) -> u64 {
            let delta = timestamp - first_edge_timestamp;
            let new_delta = delta * BAUD_DIVIDER as u64;
            let skew_delta = new_delta * ((100i32 + skew_pc) as u64) / 100u64;
            let jittered_delta =
                (skew_delta as i64) + ((period_ns as i64) * jitter_pc as i64) / 100i64;
            (first_edge_timestamp as i64 + jittered_delta) as u64
        }

        fn clock_test(skew_pc: i32, jitter_pc: i32) -> Result<()> {
            let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
            let modified_baud = BAUD_RATE / BAUD_DIVIDER;
            let period_ns = 1_000_000_000u64 / modified_baud as u64;
            let first_edge_timestamp = EVENT_TIMESTAMPS[0];

            let modified_timestamps = EVENT_TIMESTAMPS
                .iter()
                .map(|timestamp| {
                    modify_timestamp(
                        *timestamp,
                        first_edge_timestamp,
                        period_ns,
                        skew_pc,
                        jitter_pc,
                    )
                })
                .collect::<Vec<_>>();
            let modified_response_timestamp = modify_timestamp(
                READ_RESPONSE_TIMESTAMP,
                first_edge_timestamp,
                period_ns,
                skew_pc,
                jitter_pc,
            );
            let decoder = UartBitbangDecoder::new(config.clone());
            sample_and_decode(
                decoder,
                true,
                START_RESPONSE.clone(),
                &modified_timestamps,
                modified_response_timestamp,
                modified_baud,
                EXPECTED_RESPONSE.into(),
            )?;
            Ok(())
        }

        // Test -20% -> 20% jitter (unidirectional only for now)
        for jitter_pc in -20..=20i32 {
            clock_test(0i32, jitter_pc)?;
        }

        // UART frame time = 1 start bit + 8 data bits + 1 stop bit = 10 samples
        // Rounding gives up to a 50% tolerance, so realistically we can test a
        // max of -4 -> 4% skew
        for skew_pc in -4..=4i32 {
            clock_test(skew_pc, 0i32)?;
        }

        // Test with small jitter (-5 -> 5%) & skew (-2 -> 2%)
        for jitter_pc in -5..=5i32 {
            for skew_pc in -2..=2i32 {
                clock_test(skew_pc, jitter_pc)?;
            }
        }

        Ok(())
    }

    #[test]
    fn start_during_break() -> Result<()> {
        // Check that we can handle starting monitoring during a break
        let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
        let decoder = UartBitbangDecoder::new(config);

        // Insert an extra edge just before, an start in a break condition (RX = 0)
        let bit_time = EVENT_TIMESTAMPS[1] - EVENT_TIMESTAMPS[0];
        let before_timestamp = EVENT_TIMESTAMPS[0] - bit_time;
        let mut events = vec![before_timestamp];
        events.extend_from_slice(&EVENT_TIMESTAMPS);
        sample_and_decode(
            decoder,
            false,
            START_RESPONSE.clone(),
            &events,
            READ_RESPONSE_TIMESTAMP,
            BAUD_RATE,
            EXPECTED_RESPONSE.into(),
        )
    }

    #[test]
    fn start_mid_transmission() -> Result<()> {
        // Check that we can handle starting monitoring mid-transmission
        let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
        let decoder = UartBitbangDecoder::new(config.clone());

        // Insert some spurious edges a couple of UART frames before,
        // corresponding to the end of some partial UART transmission.
        // The decoder should ignore this and read as normal.
        let bit_time = EVENT_TIMESTAMPS[1] - EVENT_TIMESTAMPS[0];
        let start_response = MonitoringStartResponse {
            timestamp: EVENT_TIMESTAMPS[0] - bit_time * 24,
            initial_levels: vec![true],
        };
        let mut events = vec![
            EVENT_TIMESTAMPS[0] - bit_time * 23,
            EVENT_TIMESTAMPS[0] - bit_time * 21,
            EVENT_TIMESTAMPS[0] - bit_time * 20,
        ];
        events.extend_from_slice(&EVENT_TIMESTAMPS);
        sample_and_decode(
            decoder,
            false,
            start_response,
            &events,
            READ_RESPONSE_TIMESTAMP,
            BAUD_RATE,
            EXPECTED_RESPONSE.into(),
        )?;

        // Insert some spurious edges just before, corresponding to the end
        // of some partial UART transmission. The decoder should decode nothing
        // (instead of garbage) because it cannot find a stable state.
        let decoder = UartBitbangDecoder::new(config);
        let start_response = MonitoringStartResponse {
            timestamp: EVENT_TIMESTAMPS[0] - bit_time * 5,
            initial_levels: vec![true],
        };
        let mut events = vec![
            EVENT_TIMESTAMPS[0] - bit_time * 4,
            EVENT_TIMESTAMPS[0] - bit_time * 2,
            EVENT_TIMESTAMPS[0] - bit_time,
        ];
        events.extend_from_slice(&EVENT_TIMESTAMPS);
        let empty_response = String::new();
        sample_and_decode(
            decoder,
            false,
            start_response,
            &events,
            READ_RESPONSE_TIMESTAMP,
            BAUD_RATE,
            empty_response,
        )
    }

    #[test]
    fn partial_responses() -> Result<()> {
        // Check that we can decode the data over several partial monitor reads
        let config = UartBitbangConfig::new(8, UartStopBits::Stop1, 2, Parity::None)?;
        let decoder = UartBitbangDecoder::new(config.clone());
        let edges = [Edge::Falling, Edge::Rising];
        let events = EVENT_TIMESTAMPS
            .iter()
            .enumerate()
            .map(|(i, t)| edge(0, edges[i % 2], *t))
            .collect::<Vec<_>>();
        let mut response_decoder =
            UartRxMonitoringDecoder::new(decoder, CLOCK_NATURE, START_RESPONSE.clone())?;

        // Decode the first 60 edges 3 edges at a time
        let mut decoded = Vec::new();
        for partial_edges in events[..60].chunks(3) {
            // "read" a response at last edge + 1 ns
            let timestamp = partial_edges.last().unwrap().timestamp + 1;
            let read_response = MonitoringReadResponse {
                events: Vec::from(partial_edges),
                timestamp,
            };
            decoded.extend(response_decoder.decode_response(read_response, 0, BAUD_RATE)?);
        }

        // Decode the remaining edges with up to 20 at a time
        for partial_edges in events[60..].chunks(20) {
            let timestamp = partial_edges.last().unwrap().timestamp + 1;
            let read_response = MonitoringReadResponse {
                events: Vec::from(partial_edges),
                timestamp,
            };
            decoded.extend(response_decoder.decode_response(read_response, 0, BAUD_RATE)?);
        }

        // Final read response containing the end timestamp
        let read_response = MonitoringReadResponse {
            events: Vec::new(),
            timestamp: READ_RESPONSE_TIMESTAMP,
        };
        decoded.extend(response_decoder.decode_response(read_response, 0, BAUD_RATE)?);
        assert_eq!(
            String::from_utf8(decoded),
            Ok(String::from(EXPECTED_RESPONSE))
        );
        Ok(())
    }
}
