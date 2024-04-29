// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface spi_if
  import spi_agent_pkg::*;
  import uvm_pkg::*;
(
  input rst_n,
  inout wire [3:0] sio
);
  // standard spi interface pins
  logic       sck;
  logic [CSB_WIDTH-1:0] csb;

  // spi host drives sio to x when idle. release to z in case the io is used for other peripheral
  bit disconnected;

  logic [3:0] sio_out;
  assign sio = disconnected ? 'z : sio_out;

  // debug signals
  logic [7:0] host_byte;
  int         host_bit;
  logic [7:0] device_byte;
  int         device_bit;
  int         sck_pulses;
  bit         sck_polarity;
  bit         sck_phase;

  bit         en_chk = 1;
  string      msg_id = "spi_if";

  int unsigned clk_cycle;
  //---------------------------------
  // common tasks
  //---------------------------------
  function automatic void disconnect(bit set_disconnect = 1);
    disconnected = set_disconnect;
  endfunction : disconnect

  task automatic wait_for_clks(int clks);
    repeat (clks) @(posedge sck);
  endtask : wait_for_clks

  task automatic get_data_from_sio(spi_agent_pkg::spi_mode_e mode, output bit sio_bits[]);
    case (mode)
      Standard: sio_bits = {>> 1 {sio[0]}};
      Dual:     sio_bits = {>> 1 {sio[1:0]}};
      Quad:     sio_bits = {>> 1 {sio[3:0]}};
      default:  sio_bits = {>> 1 {sio[0]}};
    endcase
  endtask : get_data_from_sio

  function automatic bit [CSB_WIDTH-1:0] get_active_csb();
    foreach (csb[i]) begin
      if (csb[i] === 0) begin
        return i;
      end
    end
    `uvm_fatal(msg_id, "Don't call this function - get_active_csb when there is no active CSB")
  endfunction : get_active_csb

  initial forever begin
    @(posedge sck);
    if (rst_n === 1)
      if (&csb === 0)
        clk_cycle++;
  end

  // check only 1 csb can be active
  initial forever begin
    @(csb);
    if (en_chk) `DV_CHECK_LE($countones(CSB_WIDTH'(~csb)), 1, , , msg_id)
  end
endinterface : spi_if
