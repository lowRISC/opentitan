// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use serialport::Parity;
use thiserror::Error;

/// UART frame configuration to use for UART bitbanging. Assumes LSB first.
#[derive(Clone, Debug)]
pub struct UartBitbangConfig {
    pub data_bits: u8, // Assumes <= 8 data bits
    pub stop_bits: u8, // 1.5 bits is not supported
    // The number of character cycles for which RX is held low during
    // transmission of a break character
    pub break_char_cycles: u8,
    pub parity: Parity,
}

impl UartBitbangConfig {
    pub fn new(
        data_bits: u8,
        stop_bits: u8,
        break_char_cycles: u8,
        parity: Parity,
    ) -> Result<UartBitbangConfig> {
        if !(5..=8).contains(&data_bits) {
            bail!("UART bitbanging encoder only supports between 5 and 8 bit data.");
        }
        if stop_bits == 0 || stop_bits > 2 {
            bail!("UART bitbanging encoder only supports 1 or 2 stop bits.");
        }
        Ok(Self {
            data_bits,
            stop_bits,
            break_char_cycles,
            parity,
        })
    }

    /// The amount of samples (bit transmissions) in one frame.
    pub fn bit_time_per_frame(&self) -> u32 {
        let start_bit = 1;
        let parity_bits = (self.parity != Parity::None) as u8;
        (start_bit + self.data_bits + parity_bits + self.stop_bits).into()
    }

    /// For a break, hold logic low for (frame bit time) * break cycles
    pub fn break_bit_time(&self) -> u32 {
        self.bit_time_per_frame() * self.break_char_cycles as u32
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

    /// A helper to change the parity of the encoder
    pub fn set_parity(&mut self, parity: Parity) {
        self.config.parity = parity;
    }

    /// Encode the transmission of a UART break condition into a bitbanging
    /// sample, to be used on the TX pin.
    pub fn encode_break(&self, samples: &mut Vec<u8>) {
        for _ in 0..self.config.break_bit_time() {
            samples.push(0x00 << TX);
        }
        for _ in 0..self.config.stop_bits {
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
        let parity = data.count_ones() % 2;
        match self.config.parity {
            Parity::Even => samples.push(((parity != 0) as u8) << TX),
            Parity::Odd => samples.push(((parity == 0) as u8) << TX),
            Parity::None => (),
        }
        // Stop bits
        for _ in 0..self.config.stop_bits {
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
    Data { bits: u8 },
    Parity,
    Stop { data: u8, bits: u8 },
    Break { bits: u32 },
}

/// A decoder for decoding UART samples. `RX` is the bit in the input sample
/// bitfield to use for RX transmissions.
pub struct UartBitbangDecoder<const RX: u8> {
    pub config: UartBitbangConfig,
    state: DecodingState,
    parsed_data: u8,
    parsed_parity: Option<bool>,
}

impl<const RX: u8> UartBitbangDecoder<RX> {
    pub fn new(config: UartBitbangConfig) -> Self {
        Self {
            config,
            state: DecodingState::Idle,
            parsed_data: 0x00,
            parsed_parity: None,
        }
    }

    /// A helper to change the parity of the decoder
    pub fn set_parity(&mut self, parity: Parity) {
        self.config.parity = parity;
    }

    // A helper to construct a `Broken` UART transfer symbol
    fn broken(&self, error: UartTransferDecodeError) -> UartTransfer {
        UartTransfer::Broken {
            data: self.parsed_data,
            parity: self.parsed_parity,
            error,
        }
    }

    /// Finishes decoding the current UART transfer.
    fn get_decoded_character(&mut self) -> Result<UartTransfer> {
        // Detect valid & invalid break conditions
        if let DecodingState::Break { bits } = self.state {
            if bits < self.config.break_bit_time() {
                return Ok(self.broken(UartTransferDecodeError::InvalidBreak));
            }
            return Ok(UartTransfer::Break);
        }

        // Detect we've fully stopped, and handle invalid stop signals.
        if let DecodingState::Stop { data, bits } = self.state {
            if bits != self.config.stop_bits {
                bail!("`get_decoded_character` called before reading all stop bits");
            }
            if data.count_ones() as u8 != bits {
                return Ok(self.broken(UartTransferDecodeError::InvalidStop));
            }
        } else {
            bail!("`get_decoded_character` called before the end of a transmission");
        }

        // If configured to use parity, check and report single parity errors.
        if self.config.parity != Parity::None {
            let mut decoded_parity = (self.parsed_data.count_ones() % 2) != 0;
            if let Some(parity_bit) = self.parsed_parity {
                decoded_parity ^= parity_bit;
            }
            let expected_parity = self.config.parity != Parity::Even;
            if expected_parity != decoded_parity {
                return Ok(self.broken(UartTransferDecodeError::ParityMismatch));
            }
        }

        Ok(UartTransfer::Byte {
            data: self.parsed_data,
        })
    }

    /// Given a sampled waveform (where bit RX is the UART RX), advance the
    /// UART decoder state based on the contents of the sample. If the sample
    /// is the final stop bit, return the decoded UART transfer.
    pub fn decode_sample(&mut self, sample: u8) -> Result<Option<UartTransfer>> {
        let rx = (sample >> RX) & 0x1;
        match self.state {
            DecodingState::Idle => {
                if rx == 0 {
                    self.parsed_data = 0x00;
                    self.state = DecodingState::Data { bits: 0 };
                }
            }
            DecodingState::Data { mut bits } => {
                self.parsed_data |= rx << bits;
                bits += 1;
                if bits >= self.config.data_bits {
                    if self.config.parity == Parity::None {
                        self.state = DecodingState::Stop {
                            data: 0x00,
                            bits: 0,
                        };
                    } else {
                        self.state = DecodingState::Parity;
                    }
                } else {
                    self.state = DecodingState::Data { bits };
                }
            }
            DecodingState::Parity => {
                self.parsed_parity = Some(rx != 0);
                self.state = DecodingState::Stop {
                    data: 0x00,
                    bits: 0,
                };
            }
            DecodingState::Stop { mut data, mut bits } => {
                data |= rx << bits;
                bits += 1;
                self.state = DecodingState::Stop { data, bits };
                if bits >= self.config.stop_bits {
                    if self.parsed_data != 0x00 || self.parsed_parity == Some(true) || data != 0x00
                    {
                        let decoded = self.get_decoded_character()?;
                        self.state = DecodingState::Idle;
                        return Ok(Some(decoded));
                    }
                    let mut break_bits = 1 + self.config.data_bits + bits;
                    if self.config.parity != Parity::None {
                        break_bits += 1;
                    }
                    self.state = DecodingState::Break {
                        bits: break_bits as u32,
                    };
                }
            }
            DecodingState::Break { bits } => {
                if rx != 0 {
                    let decoded = self.get_decoded_character()?;
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
        self.parsed_data = 0x00;
        self.parsed_parity = None;
    }
}
