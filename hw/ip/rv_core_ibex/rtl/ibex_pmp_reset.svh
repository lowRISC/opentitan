// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Default reset values for PMP CSRs. Where the number of regions
// (PMPNumRegions) is less than 16 the reset values for the higher numbered
// regions are ignored.
//
// See the Ibex Reference Guide (Custom Reset Values under Physical Memory
// Protection) for more information.

localparam pmp_cfg_t pmp_cfg_rst[16] = '{
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 0
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 1
  '{lock: 1'b1, mode: PMP_MODE_NAPOT, exec: 1'b1, write: 1'b0, read: 1'b1}, // rgn 2  [ROM: LRX]
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 3
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 4
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 5
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 6
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 7
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 8
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 9
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 10
  '{lock: 1'b1, mode: PMP_MODE_TOR,   exec: 1'b0, write: 1'b1, read: 1'b1}, // rgn 11 [MMIO: LRW]
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 12
  '{lock: 1'b1, mode: PMP_MODE_NAPOT, exec: 1'b1, write: 1'b1, read: 1'b1}, // rgn 13 [DV_ROM: LRWX]
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // rgn 14
  '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}  // rgn 15
};

// Addresses are given in byte granularity for readibility. A minimum of two
// bits will be stripped off the bottom (PMPGranularity == 0) with more stripped
// off at coarser granularities.
//
// Note: The size of region 2 below must match `_epmp_reset_rx_size` in
// `sw/device/silicon_creator/rom/rom.ld`
localparam [33:0] pmp_addr_rst[16] = '{
  34'h00000000, // rgn 0
  34'h00000000, // rgn 1
  34'h000083fc, // rgn 2  [ROM: base=0x0000_8000 size=0x800 (2KiB)]
  34'h00000000, // rgn 3
  34'h00000000, // rgn 4
  34'h00000000, // rgn 5
  34'h00000000, // rgn 6
  34'h00000000, // rgn 7
  34'h00000000, // rgn 8
  34'h00000000, // rgn 9
  34'h40000000, // rgn 10 [MMIO: lo=0x4000_0000]
  34'h42010000, // rgn 11 [MMIO: hi=0x4201_0000]
  34'h00000000, // rgn 12
  34'h000107fc, // rgn 13 [DV_ROM: base=0x0001_0000 size=0x1000 (4KiB)]
  34'h00000000, // rgn 14
  34'h00000000  // rgn 15
};

localparam pmp_mseccfg_t pmp_mseccfg_rst = '{rlb : 1'b1, mmwp: 1'b1, mml: 1'b0};
