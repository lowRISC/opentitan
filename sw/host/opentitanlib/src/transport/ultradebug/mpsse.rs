// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use bitflags::bitflags;
use log;
use safe_ftdi as ftdi;
use std::time::{Duration, Instant};
use thiserror::Error;

use crate::bail;
use crate::io::gpio::GpioError;
use crate::io::spi::SpiError;

pub const MPSSE_WRCLK_FALLING: u8 = 0x01;
pub const MPSSE_RDCLK_FALLING: u8 = 0x04;
pub const MPSSE_DIR_LSB_FIRST: u8 = 0x08;
pub const MPSSE_WRITE_DATA: u8 = 0x10;
pub const MPSSE_READ_DATA: u8 = 0x20;
pub const MPSSE_SET_LOW_GPIO: u8 = 0x80;
pub const MPSSE_SET_HIGH_GPIO: u8 = 0x82;
pub const MPSSE_GET_LOW_GPIO: u8 = 0x81;
pub const MPSSE_GET_HIGH_GPIO: u8 = 0x83;
pub const MPSSE_SET_CLKDIV: u8 = 0x86;
pub const MPSSE_DISABLE_DIVBY5: u8 = 0x8A;
pub const MPSSE_INVALID_COMMAND: u8 = 0xAA;
pub const MPSSE_CLOCK_FREQUENCY: u32 = 12_000_000;

bitflags! {
    /// Gpio direction for output pinds on an FTDI interface.
    pub struct GpioDirection: u8 {
        const OUT_0 = 0x01;
        const OUT_1 = 0x02;
        const OUT_2 = 0x04;
        const OUT_3 = 0x08;
        const OUT_4 = 0x10;
        const OUT_5 = 0x20;
        const OUT_6 = 0x40;
        const OUT_7 = 0x80;
    }
}

/// ClockEdge defines how data will be driven or sampled on the FTDI device.
#[derive(Debug, Clone, Copy)]
pub enum ClockEdge {
    Rising,
    Falling,
}

/// BitDirection determines in which order the bits will be shifted in/out on
/// a serial interface.
#[derive(Debug, Clone, Copy)]
pub enum BitDirection {
    LsbFirst,
    MsbFirst,
}

/// DataShiftOptions determines the full set of serial options for a data
/// in/out operation.
#[derive(Debug)]
pub struct DataShiftOptions {
    pub read_clock_edge: ClockEdge,
    pub write_clock_edge: ClockEdge,
    pub bit_direction: BitDirection,
    pub write_data: bool,
    pub read_data: bool,
}

impl DataShiftOptions {
    /// Transform a `DataShiftOptions` structure into an MPSSE opcode.
    pub fn as_opcode(&self) -> u8 {
        let mut opcode = 0u8;
        opcode |= match self.read_clock_edge {
            ClockEdge::Rising => 0,
            ClockEdge::Falling => MPSSE_RDCLK_FALLING,
        };
        opcode |= match self.write_clock_edge {
            ClockEdge::Rising => 0,
            ClockEdge::Falling => MPSSE_WRCLK_FALLING,
        };
        opcode |= match self.bit_direction {
            BitDirection::LsbFirst => MPSSE_DIR_LSB_FIRST,
            BitDirection::MsbFirst => 0,
        };
        opcode |= match self.write_data {
            false => 0,
            true => MPSSE_WRITE_DATA,
        };
        opcode |= match self.read_data {
            false => 0,
            true => MPSSE_READ_DATA,
        };
        opcode
    }
}

impl Default for DataShiftOptions {
    fn default() -> Self {
        DataShiftOptions {
            read_clock_edge: ClockEdge::Rising,
            write_clock_edge: ClockEdge::Rising,
            bit_direction: BitDirection::MsbFirst,
            write_data: false,
            read_data: false,
        }
    }
}

/// MPSSE `Command`s are used to configure the device, set or get GPIOs or
/// perform serial data transfers.
pub enum Command<'rd, 'wr> {
    ReadData(DataShiftOptions, &'rd mut [u8]),
    WriteData(DataShiftOptions, &'wr [u8]),
    TransactData(DataShiftOptions, &'wr [u8], DataShiftOptions, &'rd mut [u8]),
    SetLowGpio(GpioDirection, u8),
    GetLowGpio(&'rd mut u8),
    SetClockDivisor(u16),
    DisableDivBy5,
    InvalidCommand,
}

impl Command<'_, '_> {
    const MAX_LENGTH: usize = 65536;

    /// Calculate the response length for this `Command`.
    pub fn response_length(&self) -> usize {
        match self {
            Command::ReadData(_, buf) => buf.len(),
            Command::TransactData(_, _, _, buf) => buf.len(),
            Command::GetLowGpio(_) => 1,
            Command::WriteData(_, _)
            | Command::SetLowGpio(_, _)
            | Command::SetClockDivisor(_)
            | Command::DisableDivBy5
            | Command::InvalidCommand => 0,
        }
    }

    /// Extend a `Vec<u8>` with the low-level representation of this `Command`.
    pub fn extend(&self, buf: &mut Vec<u8>) -> Result<()> {
        match self {
            Command::ReadData(options, data) => {
                if data.len() > Command::MAX_LENGTH {
                    bail!(SpiError::InvalidDataLength(data.len()));
                }
                buf.push(options.as_opcode());
                buf.extend_from_slice(&((data.len() - 1) as u16).to_le_bytes());
            }
            Command::WriteData(options, data) => {
                if data.len() > Command::MAX_LENGTH {
                    bail!(SpiError::InvalidDataLength(data.len()));
                }
                buf.push(options.as_opcode());
                buf.extend_from_slice(&((data.len() - 1) as u16).to_le_bytes());
                buf.extend(data.iter());
            }
            Command::TransactData(woptions, wdata, roptions, rdata) => {
                if wdata.len() > Command::MAX_LENGTH {
                    bail!(SpiError::InvalidDataLength(wdata.len()));
                }
                if wdata.len() != rdata.len() {
                    bail!(SpiError::MismatchedDataLength(wdata.len(), rdata.len()));
                }
                buf.push(woptions.as_opcode() | roptions.as_opcode());
                buf.extend_from_slice(&((wdata.len() - 1) as u16).to_le_bytes());
                buf.extend(wdata.iter());
            }
            Command::SetLowGpio(direction, value) => {
                buf.push(MPSSE_SET_LOW_GPIO);
                buf.push(*value);
                buf.push(direction.bits());
            }
            Command::GetLowGpio(_) => {
                buf.push(MPSSE_GET_LOW_GPIO);
            }
            Command::SetClockDivisor(divisor) => {
                buf.push(MPSSE_SET_CLKDIV);
                buf.extend_from_slice(&divisor.to_le_bytes());
            }
            Command::DisableDivBy5 => {
                buf.push(MPSSE_DISABLE_DIVBY5);
            }
            Command::InvalidCommand => {
                buf.push(MPSSE_INVALID_COMMAND);
            }
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("unknown MPSSE error: {0:02x} {1:02x}")]
    MpsseUnknown(u8, u8),
}

/// An MPSSE `Context` is the high-level interface to an MPSSE FTDI interface.
pub struct Context {
    // The FTDI interface/device.
    pub device: ftdi::Device,
    // The maximum clock frequency the device can operate at.
    pub max_clock_frequency: u32,
    // The current clock frequency the device is operating at.
    pub clock_frequency: u32,
    // The input/output pin direction of the GPIO pins.
    pub gpio_direction: GpioDirection,
    // The current value of the GPIO pins.
    pub gpio_value: u8,
    // The receive timeout of the last read operation in a command sequence.
    pub receive_timeout: Duration,
}

impl Context {
    /// Create a new MPSSE `Context` given an FTDI device.
    pub fn new(device: ftdi::Device) -> Result<Self> {
        device.set_event_char(0, false)?;
        device.set_error_char(0, false)?;
        device.set_latency_timer(1)?;
        device.set_bitmode(0, ftdi::BitMode::Reset)?;
        device.set_bitmode(0, ftdi::BitMode::Mpsse)?;
        // Give the device some time to configure itself.
        std::thread::sleep(Duration::from_millis(50));

        let mut context = Context {
            device,
            max_clock_frequency: MPSSE_CLOCK_FREQUENCY / 2,
            clock_frequency: MPSSE_CLOCK_FREQUENCY / 2,
            gpio_direction: GpioDirection::empty(),
            gpio_value: 0,
            receive_timeout: Duration::from_millis(100),
        };
        context.set_clock_frequency(context.clock_frequency)?;
        Ok(context)
    }

    fn read_timeout(&self, rxbuf: &mut [u8], timeout: Duration) -> Result<u32> {
        let deadline = Instant::now() + timeout;
        let mut rxlen = 0;
        while rxlen < rxbuf.len() {
            if Instant::now() > deadline {
                return Ok(0);
            }
            let n = self.device.read_data(&mut rxbuf[rxlen..])?;
            rxlen += n as usize;
        }
        Ok(rxlen as u32)
    }

    fn read_status(&self) -> Result<()> {
        let mut buf = [0u8; 2];
        let n = self.device.read_data(&mut buf)?;
        if n > 0 {
            Err(Error::MpsseUnknown(buf[0], buf[1]).into())
        } else {
            Ok(())
        }
    }

    /// Execute a slice of `commands` on the target FTDI device.
    pub fn execute(&self, commands: &mut [Command]) -> Result<()> {
        // Build up a transmit buffer from the slice of commands.
        // The buffer contains both MPSSE opcodes and data.
        // Calculate the size of the receive buffer needed.
        let mut txbuf = Vec::new();
        let mut rxlen = 0;
        for command in commands.iter() {
            command.extend(&mut txbuf)?;
            rxlen += command.response_length();
        }

        // Transmit and receive simultaneously.
        // When the transmit buffer is exhausted, we issue a read with a
        // timeout to consume the available data or return a timeout error.
        let mut rxbuf = vec![0u8; rxlen];
        let mut txlen = 0;
        rxlen = 0;
        while txlen < txbuf.len() || rxlen < rxbuf.len() {
            if txlen < txbuf.len() {
                let n = self.device.write_data(&txbuf[txlen..])?;
                txlen += n as usize;
            }
            if rxlen < rxbuf.len() {
                let n = if txlen < txbuf.len() {
                    self.device.read_data(&mut rxbuf[rxlen..])?
                } else {
                    self.read_timeout(&mut rxbuf[rxlen..], self.receive_timeout)?
                };
                rxlen += n as usize;
            }
        }

        // Redistribute the received data into the buffers specified in
        // the slice of commands.
        let mut pos = 0usize;
        for command in commands.iter_mut() {
            let len = command.response_length();
            match command {
                Command::ReadData(_, buf) => {
                    buf.copy_from_slice(&rxbuf[pos..(pos + len)]);
                }
                Command::TransactData(_, _, _, buf) => {
                    buf.copy_from_slice(&rxbuf[pos..(pos + len)]);
                }
                Command::GetLowGpio(value) => {
                    **value = rxbuf[pos];
                }
                _ => {}
            }
            pos += len;
        }

        // Check for errors
        self.read_status()
    }

    /// Get the GPIO state on the target FTDI device.
    pub fn gpio_get(&mut self) -> Result<u8> {
        let mut value = 0u8;
        let command = Command::GetLowGpio(&mut value);
        self.execute(&mut [command])?;
        log::debug!("gpio_get {:x}", value);
        self.gpio_value = value;
        Ok(value)
    }

    /// Set the GPIO state of an individual pin on the FTDI device.
    pub fn gpio_set(&mut self, pin: u8, high: bool) -> Result<()> {
        let dir = GpioDirection::from_bits(1 << pin).ok_or(GpioError::InvalidPinNumber(pin))?;
        if (dir & self.gpio_direction).bits() == 0 {
            return Err(GpioError::InvalidPinMode(pin).into());
        }
        if high {
            self.gpio_value |= 1 << pin;
        } else {
            self.gpio_value &= !(1 << pin);
        }
        log::debug!(
            "gpio_set dir={:x} value={:x}",
            self.gpio_direction.bits(),
            self.gpio_value
        );
        let command = Command::SetLowGpio(self.gpio_direction, self.gpio_value);
        self.execute(&mut [command])
    }

    /// Set the direction of an individual pin on the FTDI device.
    pub fn gpio_set_direction(&mut self, pin: u8, output: bool) -> Result<()> {
        let direction =
            GpioDirection::from_bits(1 << pin).ok_or(GpioError::InvalidPinNumber(pin))?;
        if output {
            self.gpio_direction |= direction;
        } else {
            self.gpio_direction &= direction;
        }
        // Perform a read to immediately synchronize the direction to the device.
        let _ = self.gpio_get()?;
        Ok(())
    }

    /// Set the clock frequency for serial opertions on the FTDI device.
    pub fn set_clock_frequency(&mut self, frequency: u32) -> Result<()> {
        let base = self.max_clock_frequency;
        let divisor = base / frequency - 1;
        let actual = base / (divisor + 1);
        log::debug!(
            "mpsse: requested clock frequency {}.  actual={}",
            frequency,
            actual
        );
        self.execute(&mut [Command::SetClockDivisor(divisor as u16)])?;
        self.clock_frequency = actual;
        Ok(())
    }

    /// Send an invalid command to the FTDI device (this is typically used in a debugging
    /// context to ensure synchronization with the FTDI device).
    pub fn invalid_command(&self) -> Result<()> {
        self.execute(&mut [Command::InvalidCommand])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    // Checks the read/write opcodes generated by DataShiftOptions.
    fn test_data_shift_options() {
        let opt = DataShiftOptions {
            read_clock_edge: ClockEdge::Rising,
            read_data: true,
            ..Default::default()
        };
        assert_eq!(opt.as_opcode(), 0x20);

        let opt = DataShiftOptions {
            read_clock_edge: ClockEdge::Falling,
            read_data: true,
            ..Default::default()
        };
        assert_eq!(opt.as_opcode(), 0x24);

        let opt = DataShiftOptions {
            read_clock_edge: ClockEdge::Falling,
            read_data: true,
            bit_direction: BitDirection::LsbFirst,
            ..Default::default()
        };
        assert_eq!(opt.as_opcode(), 0x2c);

        let opt = DataShiftOptions {
            write_clock_edge: ClockEdge::Rising,
            write_data: true,
            ..Default::default()
        };
        assert_eq!(opt.as_opcode(), 0x10);

        let opt = DataShiftOptions {
            write_clock_edge: ClockEdge::Falling,
            write_data: true,
            ..Default::default()
        };
        assert_eq!(opt.as_opcode(), 0x11);

        let opt = DataShiftOptions {
            read_clock_edge: ClockEdge::Rising,
            write_clock_edge: ClockEdge::Falling,
            read_data: true,
            write_data: true,
            ..Default::default()
        };
        assert_eq!(opt.as_opcode(), 0x31);
    }

    #[test]
    // Checks the construction of a ReadData command.
    fn test_command_read_data() -> Result<()> {
        let mut read_buf = [0u8; 8];
        let opt = DataShiftOptions {
            read_clock_edge: ClockEdge::Rising,
            read_data: true,
            ..Default::default()
        };

        let command = Command::ReadData(opt, &mut read_buf);
        assert_eq!(command.response_length(), 8);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode followed by little endian representation of (length-1).
        assert_eq!(&low_level_command, &[0x20, 7, 0]);
        Ok(())
    }

    #[test]
    // Checks the construction of a WriteData command.
    fn test_command_write_data() -> Result<()> {
        let write_buf = [1u8, 2, 3, 4, 5];
        let opt = DataShiftOptions {
            write_clock_edge: ClockEdge::Falling,
            write_data: true,
            ..Default::default()
        };

        let command = Command::WriteData(opt, &write_buf);
        assert_eq!(command.response_length(), 0);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode followed by little endian representation of (length-1) followed by data.
        assert_eq!(&low_level_command, &[0x11, 4, 0, 1, 2, 3, 4, 5]);
        Ok(())
    }

    #[test]
    // Checks the construction of a TransactData command.
    fn test_command_transact_data() -> Result<()> {
        let write_buf = [1u8, 2, 3, 4, 5];
        let write_opt = DataShiftOptions {
            write_clock_edge: ClockEdge::Falling,
            write_data: true,
            ..Default::default()
        };
        let mut read_buf = [0u8; 5];
        let read_opt = DataShiftOptions {
            read_clock_edge: ClockEdge::Rising,
            read_data: true,
            ..Default::default()
        };

        let command = Command::TransactData(write_opt, &write_buf, read_opt, &mut read_buf);
        assert_eq!(command.response_length(), 5);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode followed by little endian representation of (length-1) followed by data.
        assert_eq!(&low_level_command, &[0x31, 4, 0, 1, 2, 3, 4, 5]);
        Ok(())
    }

    #[test]
    // Checks the construction of a SetLowGpio command.
    fn test_set_gpio() -> Result<()> {
        let direction = GpioDirection::OUT_0 | GpioDirection::OUT_1;
        let command = Command::SetLowGpio(direction, 0x5a);
        assert_eq!(command.response_length(), 0);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode followed by gpio value followed by gpio direction.
        assert_eq!(&low_level_command, &[0x80, 0x5a, 0x3]);
        Ok(())
    }

    #[test]
    // Checks the construction of a GetLowGpio command.
    fn test_get_gpio() -> Result<()> {
        let mut value = 0u8;
        let command = Command::GetLowGpio(&mut value);
        assert_eq!(command.response_length(), 1);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode only.
        assert_eq!(&low_level_command, &[0x81]);
        Ok(())
    }

    #[test]
    // Checks the construction of a SetClockDivisor command.
    fn test_set_clock_divisor() -> Result<()> {
        let command = Command::SetClockDivisor(0x1234);
        assert_eq!(command.response_length(), 0);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode followed by the little-endian representation of the divisor.
        assert_eq!(&low_level_command, &[0x86, 0x34, 0x12]);
        Ok(())
    }

    #[test]
    // Checks the construction of a DisableDivBy5 command.
    fn test_disable_div_by_five() -> Result<()> {
        let command = Command::DisableDivBy5;
        assert_eq!(command.response_length(), 0);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode only.
        assert_eq!(&low_level_command, &[0x8a]);
        Ok(())
    }

    #[test]
    // Checks the construction of an InvalidCommand command.
    fn test_invalid_command() -> Result<()> {
        let command = Command::InvalidCommand;
        assert_eq!(command.response_length(), 0);

        let mut low_level_command = Vec::new();
        command.extend(&mut low_level_command)?;
        // opcode only.
        assert_eq!(&low_level_command, &[0xaa]);
        Ok(())
    }
}
