// Copyright lowRISC contributors.
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
// SW may change the value by updating !!CFG CSR. The update is applied to SPI
// clock domain when the SPI transaction begins. As first 8 beats of the
// transaction are the opcode (1 byte), the update has enough time to go
// through a CDC.
//
// The module needs /CS edge (puse) signals from outside. The assertion event
// (1 -> 0) signal should be in SPI clock domain. The deassertion event (0 ->
// 1) should be in SYS clock domain.

`include "prim_assert.sv"

module spid_addr_4b (
  input sys_clk_i,
  input sys_rst_ni,

  input spi_clk_i,

  input spi_csb_asserted_pulse_i,
  input sys_csb_deasserted_pulse_i,

  // Assume CFG.addr_4b_en is not external register.
  // And has the permissions as below:
  //    swaccess: "rw"
  //    hwaccess: "hrw"
  input        reg2hw_cfg_addr_4b_en_q_i, // registered input
  output logic hw2reg_cfg_addr_4b_en_de_o,
  output logic hw2reg_cfg_addr_4b_en_d_o,

  output logic spi_cfg_addr_4b_en_o, // broadcast

  input spi_addr_4b_set_i, // EN4B command
  input spi_addr_4b_clr_i  // EX4B command
);

  import spi_device_pkg::*;

  ////////////////
  // SYS -> SPI //
  ////////////////
  // The logic below converts SYS CSR output into SPI cfg_addr_4b_en value.
  logic spi_reg_cfg_addr_4b_en_sync;
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_sys2spi_sync (
    .clk_i  (spi_clk_i                    ),
    .rst_ni (sys_rst_ni                   ), // value to be consistent
    .d_i    (reg2hw_cfg_addr_4b_en_q_i    ),
    .q_o    (spi_reg_cfg_addr_4b_en_sync  )
  );

  ////////////////
  // SPI -> SYS //
  ////////////////
  // When a transaction is completed, check if the cfg_addr_4b value changed.
  // If changed, create an event to update cfg_addr_4b in SYS clock domain so
  // that SW can read.

  logic sys_cfg_addr_4b_en_sync;
  prim_flop_2sync #(
    .Width (1),
    .ResetValue (1'b 0)
  ) u_spi2sys_sync (
    .clk_i (sys_clk_i),
    .rst_ni (sys_rst_ni),
    .d_i    (spi_cfg_addr_4b_en_o),
    .q_o    (sys_cfg_addr_4b_en_sync)
  );

  // Compare if sys_ and  sys_cfg input are different
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      hw2reg_cfg_addr_4b_en_de_o <= 1'b 0;
      hw2reg_cfg_addr_4b_en_d_o  <= 1'b 0;
    end else if (sys_csb_deasserted_pulse_i
      && (sys_cfg_addr_4b_en_sync != reg2hw_cfg_addr_4b_en_q_i)) begin
      // update!
      hw2reg_cfg_addr_4b_en_de_o <= 1'b 1;
      hw2reg_cfg_addr_4b_en_d_o  <= sys_cfg_addr_4b_en_sync;
    end else begin
      // Keep value 0 otherwise
      hw2reg_cfg_addr_4b_en_de_o <= 1'b 0;
      hw2reg_cfg_addr_4b_en_d_o  <= 1'b 0;
    end
  end

  ////////////////
  // SPI domain //
  ////////////////
  // Generates spi_cfg_addr_4b_en to broadcast to other submodules

  logic addr_4b_en_locked;
  logic addr_4b_en_lock_condition;
  logic addr_4b_en_unlock_condition;
  logic addr_4b_en_sw_update_condition;

  assign addr_4b_en_lock_condition = spi_reg_cfg_addr_4b_en_sync ? spi_addr_4b_clr_i :
                                                                   spi_addr_4b_set_i;
  assign addr_4b_en_unlock_condition = (spi_reg_cfg_addr_4b_en_sync == spi_cfg_addr_4b_en_o);
  assign addr_4b_en_sw_update_condition = (spi_reg_cfg_addr_4b_en_sync != spi_cfg_addr_4b_en_o);


  always_ff @(posedge spi_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      addr_4b_en_locked <= 1'b 0;
    end else if (!addr_4b_en_locked & addr_4b_en_lock_condition) begin
      addr_4b_en_locked <= 1'b 1;
    end else if (addr_4b_en_locked & addr_4b_en_unlock_condition) begin
      addr_4b_en_locked <= 1'b 0;
    end
  end

  always_ff @(posedge spi_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      spi_cfg_addr_4b_en_o <= 1'b 0;
    end else if (spi_addr_4b_set_i) begin
      // This event occurs when EN4B command is received
      spi_cfg_addr_4b_en_o <= 1'b 1;
    end else if (spi_addr_4b_clr_i) begin
      // EX4B command raises the clear event
      spi_cfg_addr_4b_en_o <= 1'b 0;
    end else if (spi_csb_asserted_pulse_i & !addr_4b_en_locked &
                 addr_4b_en_sw_update_condition) begin
      // Update
      spi_cfg_addr_4b_en_o <= spi_reg_cfg_addr_4b_en_sync;
    end
  end

endmodule : spid_addr_4b
