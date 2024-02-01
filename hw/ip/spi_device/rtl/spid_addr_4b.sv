// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Flash/ Passthrough 4B Address Enable/ Disable module
//
// This module manages `cfg_addr_4b_en` used in many submodules inside
// SPI_DEVICE. EN4B/ EX4B commands configures the SPI flash device's address
// size. As the commands are self-complete (cmd byte only) and no BUSY status
// follows, HW processes those commands.
//
// SW may change the value by updating !!ADDR_MODE CSR. The update is applied to
// the SPI clock domain when the SPI transaction begins. As the first 8 beats of
// the transaction are the opcode (1 byte), the update has enough time to go
// through a CDC.
//
// The module uses the cmd_sync_pulse (the 8th posedge of the SPI clock) to
// update the address mode. The sys_clk domain then receives new values
// through a 2-flop synchronizer.

`include "prim_assert.sv"

module spid_addr_4b (
  input sys_clk_i,
  input sys_rst_ni,

  input spi_clk_i,

  input cmd_sync_pulse_i,

  input        reg2hw_addr_mode_addr_4b_en_q_i,  // registered input
  input        reg2hw_addr_mode_addr_4b_en_qe_i, // SYS has originated a change
  output logic hw2reg_addr_mode_pending_d_o,
  output logic hw2reg_addr_mode_addr_4b_en_d_o,

  output logic spi_cfg_addr_4b_en_o, // broadcast
  output logic cmd_sync_cfg_addr_4b_en_o, // early output for cmdfifo

  input spi_addr_4b_set_i, // EN4B command
  input spi_addr_4b_clr_i  // EX4B command
);

  import spi_device_pkg::*;

  /////////////////////////////////////////////////////
  // SYS -> SPI (for SYS-originated change requests) //
  /////////////////////////////////////////////////////
  logic sys_fw_new_addr_mode_req, spi_fw_new_addr_mode_req;
  logic sys_fw_new_addr_mode_ack, spi_fw_new_addr_mode_ack;
  logic sys_fw_new_addr_mode_data, spi_fw_new_addr_mode_data;

  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sys_fw_new_addr_mode_req <= 1'b0;
    end else if (reg2hw_addr_mode_addr_4b_en_qe_i) begin
      sys_fw_new_addr_mode_req <= 1'b1;
    end else if (sys_fw_new_addr_mode_ack) begin
      sys_fw_new_addr_mode_req <= 1'b0;
    end
  end

  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sys_fw_new_addr_mode_data <= 1'b0;
    end else if (reg2hw_addr_mode_addr_4b_en_qe_i) begin
      sys_fw_new_addr_mode_data <= reg2hw_addr_mode_addr_4b_en_q_i;
    end
  end

  // SYS-originated address mode changes must only occur while SPI is inactive.
  // The SPI flash protocol and hardware view would be violated otherwise.
  // Thus, the data will always be stable by the time the SPI domain picks it up.
  prim_sync_reqack_data #(
    .Width (1)
  ) u_sys2spi_sync (
    .clk_src_i        (sys_clk_i),
    .rst_src_ni       (sys_rst_ni),
    .clk_dst_i        (spi_clk_i),
    .rst_dst_ni       (sys_rst_ni),

    .req_chk_i        (1'b1),

    .src_req_i        (sys_fw_new_addr_mode_req),
    .src_ack_o        (sys_fw_new_addr_mode_ack),
    .dst_req_o        (spi_fw_new_addr_mode_req),
    .dst_ack_i        (spi_fw_new_addr_mode_ack),

    .data_i           (sys_fw_new_addr_mode_data),
    .data_o           (spi_fw_new_addr_mode_data)
  );

  assign spi_fw_new_addr_mode_ack = spi_fw_new_addr_mode_req & cmd_sync_pulse_i;
  assign hw2reg_addr_mode_pending_d_o = sys_fw_new_addr_mode_req;

  ////////////////
  // SPI -> SYS //
  ////////////////
  // The SPI domain is the source of truth, so keep the SYS domain updated
  // when a firmware change isn't pending.
  logic sys_cfg_addr_4b_en;

  prim_flop_2sync #(
    .Width (1)
  ) u_spi2sys_sync (
    .clk_i     (sys_clk_i),
    .rst_ni    (sys_rst_ni),
    .d_i       (spi_cfg_addr_4b_en_o),
    .q_o       (sys_cfg_addr_4b_en)
  );

  always_comb begin
    if (sys_fw_new_addr_mode_req) begin
      hw2reg_addr_mode_addr_4b_en_d_o = sys_fw_new_addr_mode_data;
    end else begin
      hw2reg_addr_mode_addr_4b_en_d_o = sys_cfg_addr_4b_en;
    end
  end

  ////////////////
  // SPI domain //
  ////////////////
  logic spi_cfg_addr_4b_en_d, spi_cfg_addr_4b_en_q;
  always_comb begin
    spi_cfg_addr_4b_en_d = spi_cfg_addr_4b_en_q;

    if (spi_addr_4b_set_i) begin
      // This event occurs when EN4B command is received
      spi_cfg_addr_4b_en_d = 1'b 1;
    end else if (spi_addr_4b_clr_i) begin
      // EX4B command raises the clear event
      spi_cfg_addr_4b_en_d = 1'b 0;
    end else if (spi_fw_new_addr_mode_req) begin
      // Update
      spi_cfg_addr_4b_en_d = spi_fw_new_addr_mode_data;
    end
  end

  always_ff @(posedge spi_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      spi_cfg_addr_4b_en_q <= 1'b 0;
    end else if (cmd_sync_pulse_i) begin
      spi_cfg_addr_4b_en_q <= spi_cfg_addr_4b_en_d;
    end
  end

  assign spi_cfg_addr_4b_en_o = spi_cfg_addr_4b_en_q;
  assign cmd_sync_cfg_addr_4b_en_o = spi_cfg_addr_4b_en_d;

endmodule : spid_addr_4b
