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
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 0
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 1
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 2
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 3
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 4
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 5
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 6
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 7
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 8
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 9
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 10
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 11
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 12
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 13
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}, // region 14
  '{lock: 1'b0, mode: PMP_MODE_OFF, exec: 1'b0, write: 1'b0, read: 1'b0}  // region 15
};

// Addresses are given in byte granularity for readibility. A minimum of two
// bits will be stripped off the bottom (PMPGranularity == 0) with more stripped
// off at coarser granularities.
localparam [33:0] pmp_addr_rst[16] = '{
  34'h0, // region 0
  34'h0, // region 1
  34'h0, // region 2
  34'h0, // region 3
  34'h0, // region 4
  34'h0, // region 5
  34'h0, // region 6
  34'h0, // region 7
  34'h0, // region 8
  34'h0, // region 9
  34'h0, // region 10
  34'h0, // region 11
  34'h0, // region 12
  34'h0, // region 13
  34'h0, // region 14
  34'h0  // region 15
};

localparam pmp_mseccfg_t pmp_mseccfg_rst = '{rlb : 1'b0, mmwp: 1'b0, mml: 1'b0};
