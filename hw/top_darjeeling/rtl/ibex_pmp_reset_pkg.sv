// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_pmp_reset_pkg;
  import ibex_pkg::*;
  import top_darjeeling_pkg::TOP_DARJEELING_MMIO_BASE_ADDR;
  import top_darjeeling_pkg::TOP_DARJEELING_MMIO_SIZE_BYTES;

  // Default reset values for PMP CSRs. Where the number of regions
  // (PMPNumRegions) is less than 16 the reset values for the higher numbered
  // regions are ignored.

  localparam pmp_cfg_t PmpCfgRst[16] = '{
                                                                              // Region info
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 0
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 1
    '{lock: 1'b1, mode: PMP_MODE_NAPOT, exec: 1'b1, write: 1'b0, read: 1'b1}, // 2  [ROM: LRX]
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 3
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 4
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 5
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 6
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 7
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 8
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 9
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 10
    '{lock: 1'b1, mode: PMP_MODE_TOR,   exec: 1'b0, write: 1'b1, read: 1'b1}, // 11 [MMIO: LRW]
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 12
    '{lock: 1'b1, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 13
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}, // 14
    '{lock: 1'b0, mode: PMP_MODE_OFF,   exec: 1'b0, write: 1'b0, read: 1'b0}  // 15
  };

  // Addresses are given in byte granularity for readability. A minimum of two
  // bits will be stripped off the bottom (PMPGranularity == 0) with more stripped
  // off at coarser granularities.
  //
  // Note: The size of region 2 below must match `_epmp_reset_rx_size` in
  // `sw/device/silicon_creator/rom/rom.ld`
  localparam logic [33:0] PmpAddrRst[16] = '{
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
    TOP_DARJEELING_MMIO_BASE_ADDR,                                   // rgn: 10
    TOP_DARJEELING_MMIO_BASE_ADDR + TOP_DARJEELING_MMIO_SIZE_BYTES,  // rgn: 11
    34'h00000000, // rgn 12
    34'h00000000, // rgn 13
    34'h00000000, // rgn 14
    34'h00000000  // rgn 15
  };

  localparam pmp_mseccfg_t PmpMseccfgRst = '{rlb : 1'b1, mmwp: 1'b1, mml: 1'b0};
endpackage
