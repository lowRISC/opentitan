// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
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
    let data_parity = (data.count_ones() % 2) != 0;
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
pub struct UartBitbangEncoder<const TX: u8> {
    pub config: UartBitbangConfig,
}

impl<const TX: u8> UartBitbangEncoder<TX> {
    pub fn new(config: UartBitbangConfig) -> Self {
        Self { config }
    }

    /// Encode the transmission of a UART break condition into a bitbanging
    /// sample, to be used on the TX pin.
    pub fn encode_break(&self, samples: &mut Vec<u8>) {
        for _ in 0..self.config.break_bit_time() {
            samples.push(0x00 << TX);
        }
        for _ in 0..self.config.stop_bit_time() {
            samples.push(0x01 << TX);
        }
    }

    /// Encode the transmission of a character into UART bitbanging samples, to
    /// be used on the TX pin. When configured to use X data bits, only the X
    // LSBs of `data` will be used.
    pub fn encode_character(&self, data: u8, samples: &mut Vec<u8>) {
        // Start bit
        samples.push(0x00 << TX);
        // Data bits
        for bit_index in 0..self.config.data_bits {
            let bit = (data >> bit_index) & 0x01;
            samples.push(bit << TX);
        }
        // Parity bit (if applicable)
        let parity = compute_parity(data, None);
        match self.config.parity {
            Parity::Even => samples.push((parity as u8) << TX),
            Parity::Odd => samples.push((!parity as u8) << TX),
            Parity::None => (),
        }
        // Stop bits
        for _ in 0..self.config.stop_bit_time() {
            samples.push(0x01 << TX);
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
pub struct UartBitbangDecoder<const RX: u8> {
    pub config: UartBitbangConfig,
    state: DecodingState,
}

impl<const RX: u8> UartBitbangDecoder<RX> {
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
        let rx = (sample >> RX) & 0x1;
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
