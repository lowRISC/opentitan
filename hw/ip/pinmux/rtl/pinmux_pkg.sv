// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pinmux_pkg;

  import pinmux_reg_pkg::*;

  parameter int NumIOs     = NMioPads + NDioPads;
  parameter int NDFTStraps = 2;
  parameter int NTapStraps = 2;

  // Since the target-specific top-levels often have slightly different debug signal positions, we
  // need a way to pass this info from the target specific top-level into the pinmux logic. The
  // datastructure below serves this purpose. Note that all the indices below are with respect to
  // the concatenated {DIO, MIO} packed array.
  typedef struct packed {
    bit                const_sampling; // TODO: check whether this can be eliminated.
    logic [NumIOs-1:0] tie_offs;       // TODO: check whether this can be eliminated.
    int                tck_idx;
    int                tms_idx;
    int                trst_idx;
    int                tdi_idx;
    int                tdo_idx;
    int                tap_strap0_idx;
    int                tap_strap1_idx;
    int                dft_strap0_idx;
    int                dft_strap1_idx;
  } target_cfg_t;

  parameter target_cfg_t DefaultTargetCfg = '{
    const_sampling: 1'b0,
    tie_offs:       '0,
    tck_idx:        0,
    tms_idx:        0,
    trst_idx:       0,
    tdi_idx:        0,
    tdo_idx:        0,
    tap_strap0_idx: 0,
    tap_strap1_idx: 0,
    dft_strap0_idx: 0,
    dft_strap1_idx: 0
  };

  // Wakeup Detector Modes
  typedef enum logic [2:0] {
    Posedge   = 3'b000,
    Negedge   = 3'b001,
    Edge      = 3'b010,
    HighTimed = 3'b011,
    LowTimed  = 3'b100
  } wkup_mode_e;

  // Interface with LC controller
  typedef struct packed {
    logic                  valid;
    logic [NDFTStraps-1:0] straps;
  } dft_strap_test_req_t;

  typedef enum logic [NTapStraps-1:0] {
    FuncSel   = 2'b00,
    LcTapSel  = 2'b01,
    RvTapSel  = 2'b10,
    DftTapSel = 2'b11
  } tap_strap_t;

endpackage : pinmux_pkg
