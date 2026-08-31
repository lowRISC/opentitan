// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use serde::{Deserialize, Serialize};
use serialport::Parity;
use thiserror::Error;

// The number of stop bits used for UART bitbanging.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UartStopBits {
    Stop1,
    Stop1_5,
    Stop2,
}

/// UART frame configuration to use for UART bitbanging. Assumes LSB first.
#[derive(Clone, Debug)]
pub struct UartBitbangConfig {
    pub data_bits: u8,           // Assumes <= 8 data bits
    pub stop_bits: UartStopBits, // 1.5 bits is not currently supported
    // The number of character cycles for which RX is held low during
    // transmission of a break character
    pub break_char_cycles: u8,
    pub parity: Parity,
}

impl UartBitbangConfig {
    pub fn new(
        data_bits: u8,
        stop_bits: UartStopBits,
        break_char_cycles: u8,
        parity: Parity,
    ) -> Result<UartBitbangConfig> {
        if !(5..=8).contains(&data_bits) {
            bail!("UART bitbanging only supports between 5 and 8 bit data.");
        }
        if stop_bits == UartStopBits::Stop1_5 {
            bail!("UART bitbanging only supports 1 or 2 stop bits.");
        }
        Ok(Self {
            data_bits,
            stop_bits,
            break_char_cycles,
            parity,
        })
    }

    // The number of cycles to hold high for stop bits
    fn stop_bit_time(&self) -> u8 {
        match self.stop_bits {
            UartStopBits::Stop1 => 1,
            _ => 2,
        }
    }

    /// The amount of samples (bit transmissions) in one frame.
    pub fn bit_time_per_frame(&self) -> u32 {
        let start_bit = 1;
        let parity_bits = (self.parity != Parity::None) as u8;
        let stop_bits = self.stop_bit_time();
        (start_bit + self.data_bits + parity_bits + stop_bits).into()
    }

    /// For a break, hold logic low for (frame bit time) * break cycles
    pub fn break_bit_time(&self) -> u32 {
        self.bit_time_per_frame() * self.break_char_cycles as u32
    }
}

/// Count the number of 1s in the data (& an optional parity bit).
/// Return `true` if there is an even number of 1s, and `false` otherwise.
#[inline]
pub fn compute_parity(data: u8, parity_bit: Option<bool>) -> bool {
    let data_parity = !data.count_ones().is_multiple_of(2);
    if let Some(bit) = parity_bit {
        data_parity ^ bit
    } else {
        data_parity
    }
}

#[derive(Debug, PartialEq)]
pub enum UartTransfer {
    // Assumes <= 8 data bits.
    Byte {
        data: u8,
    },
    Broken {
        data: u8,
        parity: Option<bool>,
        error: UartTransferDecodeError,
    },
    Break,
}

/// An encoder for creating UART bitbanging samples for transmission. `TX` is
/// the bit in the output sample bitfield to use for TX transmissions.
pub struct UartBitbangEncoder {
    pub config: UartBitbangConfig,
}

impl UartBitbangEncoder {
    pub fn new(config: UartBitbangConfig) -> Self {
        Self { config }
    }

    /// Encode the transmission of a UART break condition into a bitbanging
    /// sample, to be used on the TX pin.
    pub fn encode_break(&self, samples: &mut Vec<u8>) {
        let break_bits = self.config.break_bit_time() as usize;
        let stop_bits = self.config.stop_bit_time() as usize;
        samples.extend(std::iter::repeat_n(0x00, break_bits));
        samples.extend(std::iter::repeat_n(0x01, stop_bits));
    }

    /// Encode the transmission of a character into UART bitbanging samples, to
    /// be used on the TX pin. When configured to use X data bits, only the X
    // LSBs of `data` will be used.
    pub fn encode_character(&self, data: u8, samples: &mut Vec<u8>) {
        samples.reserve(self.config.bit_time_per_frame() as usize);
        // Start bit
        samples.push(0x00);
        // Data bits
        for bit_index in 0..self.config.data_bits {
            let bit = (data >> bit_index) & 0x01;
            samples.push(bit);
        }
        // Parity bit (if applicable)
        let parity = compute_parity(data, None);
        match self.config.parity {
            Parity::Even => samples.push(parity as u8),
            Parity::Odd => samples.push(!parity as u8),
            Parity::None => (),
        }
        // Stop bits
        for _ in 0..self.config.stop_bit_time() {
            samples.push(0x01);
        }
    }

    /// Helper function to encode multiple characters into UART bitbanging
    /// samples in one call.
    pub fn encode_characters(&self, chars: &[u8], samples: &mut Vec<u8>) {
        for char in chars {
            self.encode_character(*char, samples);
        }
    }

    /// Encode a UART transmission (data / break) into UART bitbanging samples,
    // to be used on the TX pin.
    pub fn encode_transfer(&self, transfer: &UartTransfer, samples: &mut Vec<u8>) -> Result<()> {
        match *transfer {
            UartTransfer::Broken { .. } => bail!("Cannot encode a broken UART transfer"),
            UartTransfer::Break => self.encode_break(samples),
            UartTransfer::Byte { data } => self.encode_character(data, samples),
        }
        Ok(())
    }

    /// Helper function to encode multiple UART transfers into UART bitbanging
    /// samples in one call.
    pub fn encode_transfers(
        &self,
        transfers: &[UartTransfer],
        samples: &mut Vec<u8>,
    ) -> Result<()> {
        for transfer in transfers {
            self.encode_transfer(transfer, samples)?;
        }
        Ok(())
    }
}

#[derive(Error, Debug, PartialEq, Serialize, Deserialize)]
pub enum UartTransferDecodeError {
    #[error("Computed parity does not match expected parity")]
    ParityMismatch,
    #[error("Stop was not held high for the full stop time")]
    InvalidStop,
    #[error(
        "RX held low too long for a valid transmission, but not long enough for a break condition"
    )]
    InvalidBreak,
}

/// Possible states for the decoder state machine to be in.
#[derive(Debug, PartialEq)]
enum DecodingState {
    Idle,
    Data {
        data: u8, // Data encountered so far
        bits: u8, // Number of data bits read so far
    },
    Parity {
        data: u8, // Previously decoded data
    },
    Stop {
        data: u8,             // Previously decoded data
        parity: Option<bool>, // Previously decoded parity
        stop_data: u8,        // Stop bit data encountered so far
        stop_bits: u8,        // Number of stop bits read so far
    },
    Break {
        bits: u32, // Logic low bits encountered so far
    },
}

/// A decoder for decoding UART samples. `RX` is the bit in the input sample
/// bitfield to use for RX transmissions.
pub struct UartBitbangDecoder {
    pub config: UartBitbangConfig,
    state: DecodingState,
}

impl UartBitbangDecoder {
    pub fn new(config: UartBitbangConfig) -> Self {
        Self {
            config,
            state: DecodingState::Idle,
        }
    }

    /// Finishes decoding a break transmission in the current UART transfer
    fn get_decoded_break(&mut self) -> Result<UartTransfer> {
        let DecodingState::Break { bits } = self.state else {
            bail!("`get_decoded_break` called before decoding a break");
        };
        if bits < self.config.break_bit_time() {
            let parity = if self.config.parity != Parity::None {
                Some(false)
            } else {
                None
            };
            Ok(UartTransfer::Broken {
                data: 0x00,
                parity,
                error: UartTransferDecodeError::InvalidBreak,
            })
        } else {
            Ok(UartTransfer::Break)
        }
    }

    /// Finishes decoding the current UART transfer.
    fn get_decoded_character(&mut self) -> Result<UartTransfer> {
        // Detect we've fully stopped, and handle invalid stop signals.
        let DecodingState::Stop {
            data,
            parity,
            stop_data,
            stop_bits,
        } = self.state
        else {
            bail!("`get_decoded_character` called before the end of a transmission");
        };
        if stop_bits != self.config.stop_bit_time() {
            bail!("`get_decoded_character` called before reading all stop bits");
        }
        if stop_data.count_ones() as u8 != stop_bits {
            return Ok(UartTransfer::Broken {
                data,
                parity,
                error: UartTransferDecodeError::InvalidStop,
            });
        }

        // If configured to use parity, check and report single parity errors.
        if self.config.parity != Parity::None {
            let decoded_parity = compute_parity(data, parity);
            let expected_parity = self.config.parity != Parity::Even;
            if expected_parity != decoded_parity {
                return Ok(UartTransfer::Broken {
                    data,
                    parity,
                    error: UartTransferDecodeError::ParityMismatch,
                });
            }
        }

        Ok(UartTransfer::Byte { data })
    }

    /// Given a sampled waveform (where bit RX is the UART RX), advance the
    /// UART decoder state based on the contents of the sample. If the sample
    /// is the final stop bit, return the decoded UART transfer.
    pub fn decode_sample(&mut self, sample: u8) -> Result<Option<UartTransfer>> {
        let rx = sample & 0x1;
        match self.state {
            DecodingState::Idle => {
                if rx == 0 {
                    self.state = DecodingState::Data {
                        data: 0x00,
                        bits: 0,
                    };
                }
            }
            DecodingState::Data { mut data, mut bits } => {
                data |= rx << bits;
                bits += 1;
                self.state = if bits >= self.config.data_bits {
                    if self.config.parity == Parity::None {
                        DecodingState::Stop {
                            data,
                            parity: None,
                            stop_data: 0x00,
                            stop_bits: 0,
                        }
                    } else {
                        DecodingState::Parity { data }
                    }
                } else {
                    DecodingState::Data { data, bits }
                }
            }
            DecodingState::Parity { data } => {
                self.state = DecodingState::Stop {
                    data,
                    parity: Some(rx != 0),
                    stop_data: 0x00,
                    stop_bits: 0,
                };
            }
            DecodingState::Stop {
                data,
                parity,
                mut stop_data,
                mut stop_bits,
            } => {
                stop_data |= rx << stop_bits;
                stop_bits += 1;
                self.state = DecodingState::Stop {
                    data,
                    parity,
                    stop_data,
                    stop_bits,
                };
                if stop_bits >= self.config.stop_bit_time() {
                    if data != 0x00 || parity == Some(true) || stop_data != 0x00 {
                        let decoded = self.get_decoded_character()?;
                        self.state = DecodingState::Idle;
                        return Ok(Some(decoded));
                    }
                    self.state = DecodingState::Break {
                        bits: self.config.bit_time_per_frame(),
                    }
                }
            }
            DecodingState::Break { bits } => {
                if rx != 0 {
                    let decoded = self.get_decoded_break()?;
                    self.state = DecodingState::Idle;
                    return Ok(Some(decoded));
                }
                self.state = DecodingState::Break { bits: bits + 1 };
            }
        }
        Ok(None)
    }

    /// A helper function to decode a sequence of UART waveform samples,
    /// advancing the decoder based on the contents. If the sample contains
    /// any final stop bits, the decoded UART transfers are returned.
    pub fn decode_samples(&mut self, samples: &Vec<u8>) -> Result<Vec<UartTransfer>> {
        let mut transfers = vec![];
        for sample in samples {
            if let Some(transfer) = self.decode_sample(*sample)? {
                transfers.push(transfer);
            }
        }
        Ok(transfers)
    }

    /// Check if the decoder is currently in the idle state or not
    pub fn is_idle(&self) -> bool {
        self.state == DecodingState::Idle
    }

    /// Reset the state of decoder
    pub fn reset(&mut self) {
        self.state = DecodingState::Idle;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn compare_decoded_result(received: &[UartTransfer], expected: &[u8]) -> Result<()> {
        assert_eq!(received.len(), expected.len());
        for (transfer, expected) in received.iter().zip(expected.iter()) {
            match transfer {
                UartTransfer::Byte { data } => {
                    assert_eq!(data, expected);
                }
                _ => bail!("Only expected to decode bytes"),
            }
        }
        Ok(())
    }

    fn uart_encode_decode(config: UartBitbangConfig, message: Option<&[u8]>) -> Result<()> {
        let encoder = UartBitbangEncoder::new(config.clone());
        let mut decoder = UartBitbangDecoder::new(config);
        let msg = message.unwrap_or(b"Hello, this is a simple UART test message.");
        let mut samples = Vec::new();
        encoder.encode_characters(msg, &mut samples);
        assert!(!samples.is_empty());
        let decoded = decoder
            .decode_samples(&samples)
            .expect("Should have decoded the bitbanged message");
        assert!(decoder.is_idle());
        compare_decoded_result(&decoded, msg)
    }

    #[test]
    fn smoke() -> Result<()> {
        // Encode and decode some test strings
        let config = UartBitbangConfig::new(8, UartStopBits::Stop2, 1, Parity::None)?;
        uart_encode_decode(config.clone(), None)?;
        uart_encode_decode(config.clone(), Some(b"abc def ghi jkl"))?;
        uart_encode_decode(config.clone(), Some(b"12345"))?;

        // Check bitbang encoding against a known sample.
        let encoder = UartBitbangEncoder::new(config);
        let bytes = [0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF];
        let mut samples = Vec::new();
        encoder.encode_characters(&bytes, &mut samples);
        let expected = [
            0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0,
            1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1,
            0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1,
            1,
        ];
        assert_eq!(samples, expected);
        Ok(())
    }

    #[test]
    fn data_bits() -> Result<()> {
        // Check invalid configurations
        assert!(UartBitbangConfig::new(4, UartStopBits::Stop2, 1, Parity::None).is_err());
        assert!(UartBitbangConfig::new(9, UartStopBits::Stop2, 1, Parity::None).is_err());
        // Check all valid configurations of 5-8 data bits
        let test_msg = b"data_bits TEST STRING";
        for data_bits in 5..=8 {
            let data_mask = ((0x1u16 << data_bits) - 1) as u8;
            let msg = test_msg.iter().map(|b| b & data_mask).collect::<Vec<_>>();
            uart_encode_decode(
                UartBitbangConfig::new(data_bits, UartStopBits::Stop2, 1, Parity::None)?,
                Some(&msg),
            )?;
        }
        Ok(())
    }

    #[test]
    fn stop_bits() -> Result<()> {
        // Check invalid configurations
        assert!(UartBitbangConfig::new(8, UartStopBits::Stop1_5, 1, Parity::None).is_err());
        // Check valid configurations
        for stop_bits in [UartStopBits::Stop1, UartStopBits::Stop2] {
            uart_encode_decode(
                UartBitbangConfig::new(8, stop_bits, 1, Parity::None)?,
                Some(b"hello from the `stop_bits()` test!"),
            )?;
        }
        // Check stop bits are being applied correctly
        let mut samples = Vec::new();
        UartBitbangEncoder::new(UartBitbangConfig::new(
            8,
            UartStopBits::Stop1,
            1,
            Parity::None,
        )?)
        .encode_character(0xA5, &mut samples);
        assert_eq!(&samples, &[0, 1, 0, 1, 0, 0, 1, 0, 1, 1]);
        samples.clear();
        UartBitbangEncoder::new(UartBitbangConfig::new(
            8,
            UartStopBits::Stop2,
            1,
            Parity::None,
        )?)
        .encode_character(0xA5, &mut samples);
        assert_eq!(&samples, &[0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1]);
        // Check error on incorrect number of stop bits
        assert_eq!(
            UartBitbangDecoder::new(UartBitbangConfig::new(
                8,
                UartStopBits::Stop2,
                1,
                Parity::None
            )?)
            .decode_samples(&vec![0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0])?,
            vec![UartTransfer::Broken {
                data: 0xA5,
                parity: None,
                error: UartTransferDecodeError::InvalidStop,
            }]
        );
        Ok(())
    }

    #[test]
    fn parity_bits() -> Result<()> {
        let tests = [
            (Parity::None, vec![0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1]),
            (Parity::Odd, vec![0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1]),
            (Parity::Even, vec![0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1]),
        ];
        for (parity, expected) in tests {
            // Basic encode/decode smoke test for the parity
            uart_encode_decode(
                UartBitbangConfig::new(8, UartStopBits::Stop2, 1, parity)?,
                Some(b"this string is used for testing parity"),
            )?;
            // Check the parity bit is calculated correctly
            let config = UartBitbangConfig::new(8, UartStopBits::Stop2, 1, parity)?;
            let mut samples = Vec::new();
            UartBitbangEncoder::new(config.clone()).encode_character(0xA5, &mut samples);
            assert_eq!(&samples, &expected);
            // Check single parity errors are caught by the decoder.
            if parity == Parity::None {
                continue;
            }
            let mut decoder = UartBitbangDecoder::new(config.clone());
            let mut invalid_samples = expected.clone();
            // Introduce an error on the parity bit
            invalid_samples[9] = !invalid_samples[9] & 0x01;
            assert_eq!(
                decoder.decode_samples(&invalid_samples)?,
                vec![UartTransfer::Broken {
                    data: 0xA5,
                    parity: Some(invalid_samples[9] != 0),
                    error: UartTransferDecodeError::ParityMismatch,
                }]
            );
            decoder.reset();
            // Introduce an error on a single data bit
            for data_bit in 0..8 {
                invalid_samples = expected.clone();
                invalid_samples[1 + data_bit] = !expected[1 + data_bit] & 0x01;
                assert_eq!(
                    decoder.decode_samples(&invalid_samples)?,
                    vec![UartTransfer::Broken {
                        data: 0xA5 ^ (0x1 << data_bit),
                        parity: Some(expected[9] != 0),
                        error: UartTransferDecodeError::ParityMismatch,
                    }]
                );
                decoder.reset();
            }
        }
        Ok(())
    }

    #[test]
    fn breaks() -> Result<()> {
        // Encode/decode tests for a variety of break times
        let break_transfer = [
            UartTransfer::Byte { data: 0x12 },
            UartTransfer::Byte { data: 0x34 },
            UartTransfer::Break,
            UartTransfer::Byte { data: 0x56 },
            UartTransfer::Byte { data: 0x78 },
        ];
        for break_cycles in 1..=5 {
            let config =
                UartBitbangConfig::new(8, UartStopBits::Stop2, break_cycles, Parity::None)?;
            let encoder = UartBitbangEncoder::new(config.clone());
            let mut decoder = UartBitbangDecoder::new(config.clone());
            let mut samples = Vec::new();
            encoder.encode_transfers(&break_transfer, &mut samples)?;
            assert!(
                samples.len() > (config.bit_time_per_frame() as usize) * (break_cycles as usize)
            );
            let decoded = decoder
                .decode_samples(&samples)
                .expect("Should have decoded the bitbanged transmission");
            assert!(decoder.is_idle());
            assert_eq!(&break_transfer, &decoded[..]);
        }
        // Check error on incorrect break time when decoding
        assert_eq!(
            UartBitbangDecoder::new(UartBitbangConfig::new(
                8,
                UartStopBits::Stop2,
                2,
                Parity::None
            )?)
            .decode_samples(&vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])?,
            vec![UartTransfer::Broken {
                data: 0x00,
                parity: None,
                error: UartTransferDecodeError::InvalidBreak,
            }]
        );
        Ok(())
    }

    #[test]
    fn partial_transfers() -> Result<()> {
        // Check that the UART decoder is stateful, and correctly handles
        // input samples of partial UART transfers.
        let mut decoder = UartBitbangDecoder::new(UartBitbangConfig::new(
            8,
            UartStopBits::Stop2,
            1,
            Parity::None,
        )?);
        assert!(decoder.is_idle());
        for sample in [0, 1, 0, 1, 0, 0, 1, 0, 1, 1] {
            assert!(decoder.decode_samples(&vec![sample])?.is_empty());
            assert!(!decoder.is_idle());
        }
        assert_eq!(
            decoder.decode_samples(&vec![1])?,
            vec![UartTransfer::Byte { data: 0xA5 }]
        );
        assert!(decoder.is_idle());
        Ok(())
    }
}
