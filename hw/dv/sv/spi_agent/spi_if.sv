// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface spi_if (input rst_n);

  // standard spi interface pins
  logic sck;
  logic csb;
  logic sdo;
  logic sdi;

  // debug signals
  logic [7:0] host_byte;
  int         host_bit;
  logic [7:0] device_byte;
  int         device_bit;
  int         sck_pulses;
  bit         sck_polarity;
  bit         sck_phase;

endinterface
