// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import spi_agent_pkg::*;

interface spi_if (
  input rst_n
);

  // standard spi interface pins
  logic       sck;
  logic [3:0] csb;
  logic [3:0] sio;

  // debug signals
  logic [7:0] host_byte;
  int         host_bit;
  logic [7:0] device_byte;
  int         device_bit;
  int         sck_pulses;
  bit         sck_polarity;
  bit         sck_phase;

  //---------------------------------
  // common tasks
  //---------------------------------
  task automatic wait_for_dly(int dly);
    repeat (dly) @(posedge sck);
  endtask : wait_for_dly
  
endinterface : spi_if
