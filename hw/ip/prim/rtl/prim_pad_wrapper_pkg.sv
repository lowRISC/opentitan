// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_pad_wrapper_pkg;

  typedef enum logic [2:0] {
    BidirStd = 3'h0,  // Standard bidirectional pad
    BidirTol = 3'h1,  // Voltage tolerant pad
    BidirOd = 3'h2,   // Open-drain capable pad
    InputStd = 3'h3,  // Input-only pad
    AnalogIn0 = 3'h4, // Analog input pad
    AnalogIn1 = 3'h5  // Analog input pad
  } pad_type_e;

  typedef enum logic [1:0] {
    NoScan = 2'h0,
    ScanIn = 2'h1,
    ScanOut = 2'h2
  } scan_role_e;

  // Pad attributes
  parameter int DriveStrDw = 4;
  parameter int SlewRateDw = 2;

  typedef struct packed {
    logic [DriveStrDw-1:0] drive_strength; // Drive strength (0000: weakest, 1111: strongest).
    logic [SlewRateDw-1:0] slew_rate;      // Slew rate (0: slowest, 11: fastest).
    logic od_en;                           // Open-drain enable
    logic schmitt_en;                      // Schmitt trigger enable.
    logic keep_en;                         // Keeper enable.
    logic pull_select;                     // Pull direction (0: pull down, 1: pull up).
    logic pull_en;                         // Pull enable.
    logic virt_od_en;                      // Virtual open drain enable.
    logic invert;                          // Input/output inversion.
  } pad_attr_t;

  parameter int AttrDw = $bits(pad_attr_t);

  // Power OK signals (library dependent)
  parameter int PokDw = 8;

  typedef logic [PokDw-1:0] pad_pok_t;

endpackage : prim_pad_wrapper_pkg
