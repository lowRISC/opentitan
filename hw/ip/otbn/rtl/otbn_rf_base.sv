// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * 32b General Purpose Register File (GPRs)
 *
 * This wraps two implementations, one for FPGA (otbn_rf_base_fpga)
 * implementation the other for ASIC (otbn_rf_base_ff).
 *
 * Both reads and writes use a 2 signal protocol: An _en signal indicates intent to do
 * a read or write operation, a _commit signals the operation should proceed. A _commit without _en
 * is permissible and means no operation is performed.
 *
 * This is used to prevent combinational loops in the error handling logic in the controller.
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 * - special purpose stack on a single register (localparam `CallStackRegIndex`)
 *   for use as a call stack
 */
module otbn_rf_base
  import otbn_pkg::*;
#(
  // Register file implementation selection, see otbn_pkg.sv.
  parameter regfile_e RegFile = RegFileFF
)(
  input logic          clk_i,
  input logic          rst_ni,

  input logic [4:0]    wr_addr_i,
  input logic          wr_en_i,
  input logic [31:0]   wr_data_i,
  input logic          wr_commit_i,

  input  logic [4:0]   rd_addr_a_i,
  input  logic         rd_en_a_i,
  output logic [31:0]  rd_data_a_o,

  input  logic [4:0]   rd_addr_b_i,
  input  logic         rd_en_b_i,
  output logic [31:0]  rd_data_b_o,

  input  logic         rd_commit_i,

  output logic         call_stack_err_o
);
  localparam int unsigned CallStackRegIndex = 1;
  localparam int unsigned CallStackDepth = 8;

  // The stack implementation is shared between FF and FPGA implementations,
  // actual register register file differs between FF and FPGA implementations.
  // Pass through signals to chosen register file, diverting any reads/writes to
  // register CallStatckRegIndex to the stack.

  logic        wr_en_masked;
  logic [31:0] rd_data_a_raw;
  logic [31:0] rd_data_b_raw;

  logic pop_stack_a;
  logic pop_stack_b;
  logic pop_stack_reqd;
  logic pop_stack;
  logic push_stack_reqd;
  logic push_stack;

  logic        stack_full;
  logic [31:0] stack_data;
  logic        stack_data_valid;

  assign pop_stack_a    = rd_en_a_i & (rd_addr_a_i == CallStackRegIndex[4:0]);
  assign pop_stack_b    = rd_en_b_i & (rd_addr_b_i == CallStackRegIndex[4:0]);
  // pop_stack_reqd indicates a call stack pop is requested and pop_stack commands it to happen.
  assign pop_stack_reqd = (pop_stack_a | pop_stack_b);
  assign pop_stack      = rd_commit_i & pop_stack_reqd;

  // push_stack_reqd indicates a call stack push is requested and push_stack commands it to happen.
  assign push_stack_reqd = wr_en_i & (wr_addr_i == CallStackRegIndex[4:0]);
  assign push_stack      = wr_commit_i & push_stack_reqd;

  assign call_stack_err_o =
      (push_stack_reqd & stack_full & ~pop_stack_reqd) | (pop_stack_reqd & ~stack_data_valid);

  // Prevent any write to the stack register from going to the register file,
  // all other committed writes are passed straight through
  assign wr_en_masked = wr_en_i & wr_commit_i & ~push_stack;

  // Ignore read data from the register file if reading from the stack register,
  // otherwise pass data through from register file.
  assign rd_data_a_o = pop_stack_a ? stack_data : rd_data_a_raw;
  assign rd_data_b_o = pop_stack_b ? stack_data : rd_data_b_raw;

  otbn_stack #(
    .StackWidth (32),
    .StackDepth (CallStackDepth)
  ) u_call_stack (
    .clk_i,
    .rst_ni,

    .full_o       (stack_full),

    .push_i       (push_stack),
    .push_data_i  (wr_data_i),

    .pop_i        (pop_stack),
    .top_data_o   (stack_data),
    .top_valid_o  (stack_data_valid)
  );

  if (RegFile == RegFileFF) begin : gen_rf_base_ff
    otbn_rf_base_ff u_otbn_rf_base_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i   (wr_en_masked),
      .wr_data_i,

      .rd_addr_a_i,
      .rd_data_a_o (rd_data_a_raw),
      .rd_addr_b_i,
      .rd_data_b_o (rd_data_b_raw)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_rf_base_fpga
    otbn_rf_base_fpga u_otbn_rf_base_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i   (wr_en_masked),
      .wr_data_i,

      .rd_addr_a_i,
      .rd_data_a_o (rd_data_a_raw),
      .rd_addr_b_i,
      .rd_data_b_o (rd_data_b_raw)
    );
  end
endmodule
