// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};

use super::spi::{SpiError, Target, Transfer};

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
/// Declarations of if and when to switch from single-lane SPI to a faster mode.
pub enum Switch {
    Mode111,
    Mode11N,
    Mode1NN,
    ModeNNN,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum DataWidth {
    Single, // Standard SPI
    Dual,   // Use both COPI and CIPO for data
    Quad,
    Octo,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Cmd {
    data: [u8; 8],
    opcode_len: u8,
    addr_len: u8,
    mode: Mode,
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddressMode {
    #[default]
    Mode3b = 3,
    Mode4b = 4,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Mode {
    /// The number of no-operation clock cycles between address and data phases.
    pub dummy_cycles: u8,
    /// Declarations of if and when to switch from single-lane SPI to a faster mode as declared by
    /// `width` and `double_transfer_rate`.
    pub switch: Switch,
    /// How many lanes to use after the switch (1, 2, 4, or 8).
    pub width: DataWidth,
    /// Whether to shift data on both rising and falling clock edges after the switch.
    pub double_transfer_rate: bool,
}

impl Mode {
    /// One-byte opcode, without address
    pub fn cmd(&self, opcode: u8) -> Cmd {
        let mut result = Cmd {
            data: [0u8; 8],
            opcode_len: 1,
            addr_len: 0,
            mode: *self,
        };
        result.data[0] = opcode;
        result
    }
    /// One-byte opcode, with address
    pub fn cmd_addr(&self, opcode: u8, addr: u32, addr_mode: AddressMode) -> Cmd {
        let mut result = Cmd {
            data: [0u8; 8],
            opcode_len: 1,
            addr_len: addr_mode as u8,
            mode: *self,
        };
        result.data[0] = opcode;
        result.data[1..1 + result.addr_len as usize]
            .clone_from_slice(&addr.to_be_bytes()[4 - result.addr_len as usize..]);
        result
    }
    /// Two-byte opcode, without address
    pub fn cmd2(&self, opcode1: u8, opcode2: u8) -> Cmd {
        let mut result = Cmd {
            data: [0u8; 8],
            opcode_len: 2,
            addr_len: 0,
            mode: *self,
        };
        result.data[0] = opcode1;
        result.data[1] = opcode2;
        result
    }
    /// Two-byte opcode, with address
    pub fn cmd2_addr(&self, opcode1: u8, opcode2: u8, addr: u32, addr_mode: AddressMode) -> Cmd {
        let mut result = Cmd {
            data: [0u8; 8],
            opcode_len: 2,
            addr_len: addr_mode as u8,
            mode: *self,
        };
        result.data[0] = opcode1;
        result.data[1] = opcode2;
        result.data[2..2 + result.addr_len as usize]
            .clone_from_slice(&addr.to_be_bytes()[4 - result.addr_len as usize..]);
        result
    }

    pub fn dummy_cycles(&self, dummy_cycles: u8) -> Mode {
        Mode {
            dummy_cycles,
            switch: self.switch,
            width: self.width,
            double_transfer_rate: self.double_transfer_rate,
        }
    }
}

/// Single-wire
pub const MODE_111: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode111,
    width: DataWidth::Single,
    double_transfer_rate: false,
};

/// Double transfer rate on data phase
pub const MODE_1S1S1D: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode11N,
    width: DataWidth::Single,
    double_transfer_rate: true,
};

/// Double transfer rate on address and data phase
pub const MODE_1S1D1D: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode1NN,
    width: DataWidth::Single,
    double_transfer_rate: true,
};

/// Single-wire address, dual-wire data
pub const MODE_112: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode11N,
    width: DataWidth::Dual,
    double_transfer_rate: false,
};

pub const MODE_122: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode1NN,
    width: DataWidth::Dual,
    double_transfer_rate: false,
};

pub const MODE_222: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::ModeNNN,
    width: DataWidth::Dual,
    double_transfer_rate: false,
};

/// Single-wire address, quad-wire data
pub const MODE_114: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode11N,
    width: DataWidth::Quad,
    double_transfer_rate: false,
};

pub const MODE_144: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::Mode1NN,
    width: DataWidth::Quad,
    double_transfer_rate: false,
};

pub const MODE_444: Mode = Mode {
    dummy_cycles: 0,
    switch: Switch::ModeNNN,
    width: DataWidth::Quad,
    double_transfer_rate: false,
};

impl Cmd {
    /// Method use to get binary representation of the command for use on "plain" SPI.  Will be
    /// used in cases where the transport backend does not have specialied EEPROM/Flash
    /// communication primitives.
    pub fn to_bytes(&self) -> Result<&[u8]> {
        if self.mode.switch == Switch::Mode111 && self.mode.dummy_cycles % 8 == 0 {
            Ok(&self.data
                [0..(self.opcode_len + self.addr_len + self.mode.dummy_cycles / 8) as usize])
        } else {
            Err(SpiError::InvalidOption(
                "This target does not support the requested mode".to_string(),
            )
            .into())
        }
    }

    pub fn get_opcode_len(&self) -> u8 {
        self.opcode_len
    }

    pub fn get_opcode(&self) -> &[u8] {
        &self.data[..self.opcode_len as usize]
    }

    pub fn get_address_len(&self) -> u8 {
        self.addr_len
    }

    pub fn get_address(&self) -> u32 {
        let mut addr_bytes = [0u8; 4];
        addr_bytes[4 - self.addr_len as usize..].clone_from_slice(
            &self.data[self.opcode_len as usize..(self.opcode_len + self.addr_len) as usize],
        );
        u32::from_be_bytes(addr_bytes)
    }

    pub fn get_dummy_cycles(&self) -> u8 {
        self.mode.dummy_cycles
    }

    pub fn get_switch(&self) -> Switch {
        self.mode.switch
    }

    pub fn get_width(&self) -> DataWidth {
        self.mode.width
    }

    pub fn get_double_transfer_rate(&self) -> bool {
        self.mode.double_transfer_rate
    }
}

pub enum Transaction<'rd, 'wr> {
    Command(Cmd),
    Read(Cmd, &'rd mut [u8]),
    Write(Cmd, &'wr [u8]),
    WaitForBusyClear,
}

pub const READ_STATUS: u8 = 0x05;
pub const STATUS_WIP: u8 = 0x01;

pub fn default_run_eeprom_transactions<T: Target + ?Sized>(
    spi: &T,
    transactions: &mut [Transaction],
) -> Result<()> {
    // Default implementation translates into generic SPI read/write, which works as long as
    // the transport supports generic SPI transfers of sufficint length, and that the mode is
    // single-data-wire.
    for transfer in transactions {
        match transfer {
            Transaction::Command(cmd) => {
                spi.run_transaction(&mut [Transfer::Write(cmd.to_bytes()?)])?
            }
            Transaction::Read(cmd, rbuf) => {
                spi.run_transaction(&mut [Transfer::Write(cmd.to_bytes()?), Transfer::Read(rbuf)])?
            }
            Transaction::Write(cmd, wbuf) => {
                spi.run_transaction(&mut [Transfer::Write(cmd.to_bytes()?), Transfer::Write(wbuf)])?
            }
            Transaction::WaitForBusyClear => {
                let mut status = STATUS_WIP;
                while status & STATUS_WIP != 0 {
                    spi.run_transaction(&mut [
                        Transfer::Write(&[READ_STATUS]),
                        Transfer::Read(std::slice::from_mut(&mut status)),
                    ])?;
                }
            }
        }
    }
    Ok(())
}
