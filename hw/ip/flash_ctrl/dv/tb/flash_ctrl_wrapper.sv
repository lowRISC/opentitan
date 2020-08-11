// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module flash_ctrl_wrapper (
    // Clock and Reset
    input clk_i,
    input rst_ni,

    // Bus Interface
    input  tlul_pkg::tl_h2d_t flash_ctrl_tl_i,
    output tlul_pkg::tl_d2h_t flash_ctrl_tl_o,

    input  tlul_pkg::tl_h2d_t eflash_tl_i,
    output tlul_pkg::tl_d2h_t eflash_tl_o,

    // OTP interface
    input flash_ctrl_pkg::otp_flash_t otp_i,

    // Interrupts
    output logic intr_prog_empty_o,  // Program fifo is empty
    output logic intr_prog_lvl_o,  // Program fifo is empty
    output logic intr_rd_full_o,  // Read fifo is full
    output logic intr_rd_lvl_o,  // Read fifo is full
    output logic intr_op_done_o,  // Requested flash operation (wr/erase) done
    output logic intr_op_error_o  // Requested flash operation (wr/erase) done
);

  // define inter-module signals
  flash_ctrl_pkg::flash_req_t flash_ctrl_flash_req;
  flash_ctrl_pkg::flash_rsp_t flash_ctrl_flash_rsp;

  flash_ctrl u_flash_ctrl (
      .tl_i(flash_ctrl_tl_i),
      .tl_o(flash_ctrl_tl_o),

      // Interrupt
      .intr_prog_empty_o(intr_prog_empty_o),
      .intr_prog_lvl_o  (intr_prog_lvl_o),
      .intr_rd_full_o   (intr_rd_full_o),
      .intr_rd_lvl_o    (intr_rd_lvl_o),
      .intr_op_done_o   (intr_op_done_o),
      .intr_op_error_o  (intr_op_error_o),

      // Inter-module signals
      .flash_o(flash_ctrl_flash_req),
      .flash_i(flash_ctrl_flash_rsp),
      .otp_i  (otp_i),

      .clk_i (clk_i),
      .rst_ni(rst_ni)
  );

  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;

  tlul_adapter_sram #(
      .SramAw(flash_ctrl_pkg::BusAddrW),
      .SramDw(flash_ctrl_pkg::BusWidth),
      .Outstanding(2),
      .ByteAccess(0),
      .ErrOnWrite(1)
  ) u_tl_adapter_eflash (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .tl_i(eflash_tl_i),
      .tl_o(eflash_tl_o),

      .req_o   (flash_host_req),
      .gnt_i   (flash_host_req_rdy),
      .we_o    (),
      .addr_o  (flash_host_addr),
      .wdata_o (),
      .wmask_o (),
      .rdata_i (flash_host_rdata),
      .rvalid_i(flash_host_req_done),
      .rerror_i(2'b00)
  );

  flash_phy u_flash_eflash (
      .clk_i          (clk_i),
      .rst_ni         (rst_ni),
      .host_req_i     (flash_host_req),
      .host_addr_i    (flash_host_addr),
      .host_req_rdy_o (flash_host_req_rdy),
      .host_req_done_o(flash_host_req_done),
      .host_rdata_o   (flash_host_rdata),
      .flash_ctrl_i   (flash_ctrl_flash_req),
      .flash_ctrl_o   (flash_ctrl_flash_rsp)
  );

endmodule
