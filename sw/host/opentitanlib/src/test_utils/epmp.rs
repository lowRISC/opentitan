// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use thiserror::Error;

pub mod constants {
    /// In `pmpNcfg`, bit 7 represents a locked entry.
    pub const EPMP_CFG_LOCKED: u8 = 1 << 7;
    /// In `pmpNcfg`, bit 2 represents an executable region.
    pub const EPMP_CFG_EXEC: u8 = 1 << 2;
    /// In `pmpNcfg`, bit 2 represents an writable region.
    pub const EPMP_CFG_WRITE: u8 = 1 << 1;
    /// In `pmpNcfg`, bit 2 represents an readable region.
    pub const EPMP_CFG_READ: u8 = 1 << 0;
    /// Some common configurations.
    pub const EPMP_CFG_UNLOCKED: u8 = 0;
    pub const EPMP_CFG_LOCKED_NONE: u8 = EPMP_CFG_LOCKED;
    pub const EPMP_CFG_LRO: u8 = EPMP_CFG_LOCKED | EPMP_CFG_READ;
    pub const EPMP_CFG_LRW: u8 = EPMP_CFG_LOCKED | EPMP_CFG_READ | EPMP_CFG_WRITE;
    pub const EPMP_CFG_LRX: u8 = EPMP_CFG_LOCKED | EPMP_CFG_READ | EPMP_CFG_EXEC;
    pub const EPMP_CFG_LRWX: u8 = EPMP_CFG_LOCKED | EPMP_CFG_READ | EPMP_CFG_WRITE | EPMP_CFG_EXEC;

    pub const EPMP_CFG_RO: u8 = EPMP_CFG_READ;
    pub const EPMP_CFG_RW: u8 = EPMP_CFG_READ | EPMP_CFG_WRITE;
    pub const EPMP_CFG_RX: u8 = EPMP_CFG_READ | EPMP_CFG_EXEC;
    pub const EPMP_CFG_RWX: u8 = EPMP_CFG_READ | EPMP_CFG_WRITE | EPMP_CFG_EXEC;

    /// Machine Mode Lockdown: ePMP regions with the L bit are machine-mode only.
    pub const EPMP_MSECCFG_MML: u32 = 1;
    /// Machine Mode Whitelist Policy: deny instead of ignore memory accesses with no matching
    /// rule.
    pub const EPMP_MSECCFG_MMWP: u32 = 2;
    /// Rule Locking Bypass: allow modification of locked ePMP entries.
    pub const EPMP_MSECCFG_RLB: u32 = 4;
}

#[derive(Debug, Error)]
pub enum EpmpError {
    #[error("Invalid raw EPMP length (cfg={0}, addr={1})")]
    InvalidLength(usize, usize),
}

/// Represents the different EPMP region kinds.
#[repr(u8)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EpmpRegionKind {
    Off = 0,
    Tor = 1,
    Na4 = 2,
    Napot = 3,
}

impl Default for EpmpRegionKind {
    fn default() -> Self {
        EpmpRegionKind::Off
    }
}

const EPMP_ADDR_SHIFT: u8 = 3;
const EPMP_ADDR_MASK: u8 = 3;

/// Represents the address range associated with the PMP entry.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EpmpAddressRange(pub u64, pub u64);

impl EpmpAddressRange {
    pub fn start(&self) -> u64 {
        self.0
    }
    pub fn end(&self) -> u64 {
        self.1
    }
}

/// A decoded ePMP entry.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EpmpEntry {
    /// The bit pattern present in `pmpNcfg`.
    pub cfg: u8,
    /// The region kind encoded ni the `cfg` field.
    pub kind: EpmpRegionKind,
    /// The address range for this entry.
    pub range: EpmpAddressRange,
}

#[derive(Clone, Debug, Default)]
pub struct Epmp {
    pub entry: Vec<EpmpEntry>,
}

impl Epmp {
    /// Creates an `Epmp` from the raw RISCV32 form of the ePMP.
    pub fn from_raw_rv32(pmpcfg: &[u32], pmpaddr: &[u32]) -> Result<Self> {
        ensure!(
            pmpcfg.len() * 4 == pmpaddr.len(),
            EpmpError::InvalidLength(pmpcfg.len(), pmpaddr.len())
        );
        let pmpcfg = pmpcfg
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect::<Vec<u8>>();
        let mut entry = Vec::with_capacity(pmpaddr.len());
        for i in 0..pmpaddr.len() {
            let region_kind = match (pmpcfg[i] >> EPMP_ADDR_SHIFT) & EPMP_ADDR_MASK {
                0 => EpmpRegionKind::Off,
                1 => EpmpRegionKind::Tor,
                2 => EpmpRegionKind::Na4,
                3 => EpmpRegionKind::Napot,
                _ => unreachable!(),
            };
            let addr = match region_kind {
                EpmpRegionKind::Off => EpmpAddressRange(0, 0),
                EpmpRegionKind::Tor => {
                    if i == 0 {
                        EpmpAddressRange(0, (pmpaddr[i] as u64) << 2)
                    } else {
                        EpmpAddressRange((pmpaddr[i - 1] as u64) << 2, (pmpaddr[i] as u64) << 2)
                    }
                }
                EpmpRegionKind::Na4 => {
                    EpmpAddressRange((pmpaddr[i] as u64) << 2, ((pmpaddr[i] as u64) << 2) + 4)
                }
                EpmpRegionKind::Napot => {
                    let size = pmpaddr[i].trailing_ones();
                    let addr = ((pmpaddr[i] & (pmpaddr[i] + 1)) as u64) << 2;
                    let length = (1 << (size + 3)) as u64;
                    EpmpAddressRange(addr, addr + length)
                }
            };
            entry.push(EpmpEntry {
                cfg: pmpcfg[i] & !(EPMP_ADDR_MASK << EPMP_ADDR_SHIFT),
                kind: region_kind,
                range: addr,
            });
        }
        Ok(Epmp { entry })
    }
}

#[cfg(test)]
mod tests {
    use super::constants::*;
    use super::*;

    // This particular set of PMPCFG / PMPADDR values was captured from the ROM
    // and manually modified to encompass all of the decode options.
    // The modifications are:
    // - Addition of entry 6: a duplicate of entry 2 with the perms set to RWX.
    const PMPCFG: [u32; 4] = [0x998d00, 0x1f998d, 0x8b000000, 0x9b909f00];
    const PMPADDR: [u32; 16] = [
        0x2000, 0x3411, 0x2fff, 0x8000100, 0x8001203, 0x801ffff, 0x2fff, 0x0, 0x0, 0x0, 0x10000000,
        0x14000000, 0x0, 0x41ff, 0x4007000, 0x4003fff,
    ];

    #[test]
    fn test_epmp_decode() -> Result<()> {
        let epmp = Epmp::from_raw_rv32(&PMPCFG, &PMPADDR)?;

        // The 0th entry is the bottom of a TOR range.  The decoded version of entry 0 should
        // appear as an "off" region.
        assert!(matches!(
            epmp.entry[0],
            EpmpEntry {
                cfg: 0,
                kind: EpmpRegionKind::Off,
                range: EpmpAddressRange(0, 0)
            }
        ));
        // The first entry is a TOR region representing the .text section of the ROM.
        assert!(matches!(
            epmp.entry[1],
            EpmpEntry {
                cfg: EPMP_CFG_LRX,
                kind: EpmpRegionKind::Tor,
                range: EpmpAddressRange(0x8000, 0xd044)
            }
        ));
        // The second entry is a Napot region representing the entire 32K of ROM.
        assert!(matches!(
            epmp.entry[2],
            EpmpEntry {
                cfg: EPMP_CFG_LRO,
                kind: EpmpRegionKind::Napot,
                range: EpmpAddressRange(0x8000, 0x10000)
            }
        ));
        // The sixth entry is a Napot region representing the entire 32K of ROM, but is set to
        // RWX (tests the decode of the `cfg` field with lock bit clear).
        assert!(matches!(
            epmp.entry[6],
            EpmpEntry {
                cfg: EPMP_CFG_RWX,
                kind: EpmpRegionKind::Napot,
                range: EpmpAddressRange(0x8000, 0x10000)
            }
        ));

        // The thirteenth entry is a Napot region represening the 4K RVDM RAM (LRWX).
        assert!(matches!(
            epmp.entry[13],
            EpmpEntry {
                cfg: EPMP_CFG_LRWX,
                kind: EpmpRegionKind::Napot,
                range: EpmpAddressRange(0x10000, 0x11000)
            }
        ));

        // The 14th entry is an Na4 region in RAM representing the no-access stack guard.
        eprintln!("entry14 = {:?}", epmp.entry[14]);
        assert!(matches!(
            epmp.entry[14],
            EpmpEntry {
                cfg: EPMP_CFG_LOCKED_NONE,
                kind: EpmpRegionKind::Na4,
                range: EpmpAddressRange(0x1001_c000, 0x1001_c004)
            }
        ));
        // The 15th entry is an Napot region in RAM representing a read-write region.
        assert!(matches!(
            epmp.entry[15],
            EpmpEntry {
                cfg: EPMP_CFG_LRW,
                kind: EpmpRegionKind::Napot,
                range: EpmpAddressRange(0x1000_0000, 0x1002_0000)
            }
        ));
        Ok(())
    }
}
