// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

package rom_ctrl_pkg;

  parameter int AlertFatal = 0;

  typedef struct packed {
    prim_mubi_pkg::mubi4_t done;
    prim_mubi_pkg::mubi4_t good;
  } pwrmgr_data_t;

  parameter pwrmgr_data_t PWRMGR_DATA_DEFAULT = '{
    done: prim_mubi_pkg::MuBi4True,
    good: prim_mubi_pkg::MuBi4True
  };

  typedef struct packed {
    logic [255:0] data;
    logic         valid;
  } keymgr_data_t;

  //
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 7 -n 6 -s 2 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  // However, we glom on an extra 4 bits to hold a mubi4_t that encodes "state == Done". The idea is
  // that we can use them for the rom_select_bus_o signal without needing an intermediate 1-bit
  // signal which would need burying.

  typedef enum logic [9:0] {
    ReadingLow  = {6'b001100, prim_mubi_pkg::MuBi4False},
    ReadingHigh = {6'b001011, prim_mubi_pkg::MuBi4False},
    RomAhead    = {6'b111001, prim_mubi_pkg::MuBi4False},
    KmacAhead   = {6'b100111, prim_mubi_pkg::MuBi4False},
    Checking    = {6'b010101, prim_mubi_pkg::MuBi4False},
    Done        = {6'b100000, prim_mubi_pkg::MuBi4True},
    Invalid     = {6'b010010, prim_mubi_pkg::MuBi4False}
  } fsm_state_e;


endpackage
