// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use serde::{Deserialize, Serialize};

use super::spi::SpiError;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum DataWidth {
    Single,    // Standard SPI
    SingleDtr, // Data on both rising and falling edges
    Dual,      // Use both COPI and CIPO for data
    DualDtr,   // Both COPI and CIPO, both clock edges
    Quad,
    QuadDtr,
    Octo,
    OctoDtr,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Cmd {
    data: [u8; 8],
    opcode_len: u8,
    opcode_width: DataWidth,
    addr_len: u8,
    addr_width: DataWidth,
    dummy_cycles: u8,
    data_width: DataWidth,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddressMode {
    Mode3b = 3,
    Mode4b = 4,
}

impl Default for AddressMode {
    fn default() -> Self {
        AddressMode::Mode3b
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Mode {
    pub opcode_width: DataWidth,
    pub addr_width: DataWidth,
    pub dummy_cycles: u8,
    pub data_width: DataWidth,
}

impl Mode {
    /// One-byte opcode, without address
    pub fn cmd(&self, opcode: u8) -> Cmd {
        let mut result = Cmd {
            data: [0u8; 8],
            opcode_len: 1,
            opcode_width: self.opcode_width,
            addr_len: 0,
            addr_width: self.addr_width,
            dummy_cycles: self.dummy_cycles,
            data_width: self.data_width,
        };
        result.data[0] = opcode;
        result
    }
    /// One-byte opcode, with address
    pub fn cmd_addr(&self, opcode: u8, addr: u32, addr_mode: AddressMode) -> Cmd {
        let mut result = Cmd {
            data: [0u8; 8],
            opcode_len: 1,
            opcode_width: self.opcode_width,
            addr_len: addr_mode as u8,
            addr_width: self.addr_width,
            dummy_cycles: self.dummy_cycles,
            data_width: self.data_width,
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
            opcode_width: self.opcode_width,
            addr_len: 0,
            addr_width: self.addr_width,
            dummy_cycles: self.dummy_cycles,
            data_width: self.data_width,
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
            opcode_width: self.opcode_width,
            addr_len: addr_mode as u8,
            addr_width: self.addr_width,
            dummy_cycles: self.dummy_cycles,
            data_width: self.data_width,
        };
        result.data[0] = opcode1;
        result.data[1] = opcode2;
        result.data[2..2 + result.addr_len as usize]
            .clone_from_slice(&addr.to_be_bytes()[4 - result.addr_len as usize..]);
        result
    }

    pub fn dummy_cycles(&self, dummy_cycles: u8) -> Mode {
        Mode {
            opcode_width: self.opcode_width,
            addr_width: self.addr_width,
            dummy_cycles,
            data_width: self.data_width,
        }
    }
}

/// Single-wire
pub const MODE_111: Mode = Mode {
    opcode_width: DataWidth::Single,
    addr_width: DataWidth::Single,
    dummy_cycles: 0,
    data_width: DataWidth::Single,
};

/// Single-wire address, dual-wire data
pub const MODE_112: Mode = Mode {
    opcode_width: DataWidth::Single,
    addr_width: DataWidth::Single,
    dummy_cycles: 0,
    data_width: DataWidth::Dual,
};

pub const MODE_122: Mode = Mode {
    opcode_width: DataWidth::Single,
    addr_width: DataWidth::Dual,
    dummy_cycles: 0,
    data_width: DataWidth::Dual,
};

pub const MODE_222: Mode = Mode {
    opcode_width: DataWidth::Dual,
    addr_width: DataWidth::Dual,
    dummy_cycles: 0,
    data_width: DataWidth::Dual,
};

/// Single-wire address, quad-wire data
pub const MODE_114: Mode = Mode {
    opcode_width: DataWidth::Single,
    addr_width: DataWidth::Single,
    dummy_cycles: 0,
    data_width: DataWidth::Quad,
};

pub const MODE_144: Mode = Mode {
    opcode_width: DataWidth::Single,
    addr_width: DataWidth::Quad,
    dummy_cycles: 0,
    data_width: DataWidth::Quad,
};

pub const MODE_444: Mode = Mode {
    opcode_width: DataWidth::Quad,
    addr_width: DataWidth::Quad,
    dummy_cycles: 0,
    data_width: DataWidth::Quad,
};

impl Cmd {
    /// Method use to get binary representation of the command for use on "plain" SPI.  Will be
    /// used in cases where the transport backend does not have specialied EEPROM/Flash
    /// communication primitives.
    pub fn to_bytes(&self) -> Result<&[u8]> {
        if self.opcode_width == DataWidth::Single
            && self.addr_width == DataWidth::Single
            && self.dummy_cycles % 8 == 0
            && self.data_width == DataWidth::Single
        {
            Ok(&self.data[0..(self.opcode_len + self.addr_len + self.dummy_cycles / 8) as usize])
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

    pub fn get_opcode_width(&self) -> DataWidth {
        self.opcode_width
    }

    pub fn get_opcode(&self) -> &[u8] {
        &self.data[..self.opcode_len as usize]
    }

    pub fn get_address_len(&self) -> u8 {
        self.addr_len
    }

    pub fn get_address_width(&self) -> DataWidth {
        self.addr_width
    }

    pub fn get_address(&self) -> u32 {
        let mut addr_bytes = [0u8; 4];
        addr_bytes[4 - self.addr_len as usize..].clone_from_slice(
            &self.data[self.opcode_len as usize..(self.opcode_len + self.addr_len) as usize],
        );
        u32::from_be_bytes(addr_bytes)
    }

    pub fn get_dummy_cycles(&self) -> u8 {
        self.dummy_cycles
    }

    pub fn get_data_width(&self) -> DataWidth {
        self.data_width
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
