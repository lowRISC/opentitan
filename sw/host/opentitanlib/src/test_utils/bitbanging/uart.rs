// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use serialport::Parity;

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
    Byte { data: u8 },
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
    pub fn encode_transfer(&self, transfer: &UartTransfer, samples: &mut Vec<u8>) {
        match *transfer {
            UartTransfer::Break => self.encode_break(samples),
            UartTransfer::Byte { data } => self.encode_character(data, samples),
        }
    }

    /// Helper function to encode multiple UART transfers into UART bitbanging
    /// samples in one call.
    pub fn encode_transfers(&self, transfers: &[UartTransfer], samples: &mut Vec<u8>) {
        for transfer in transfers {
            self.encode_transfer(transfer, samples);
        }
    }
}
