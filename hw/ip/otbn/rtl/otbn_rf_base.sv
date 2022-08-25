// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * 32b General Purpose Register File (GPRs) with integrity code detecting triple bit errors.
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
 * Integrity protection uses an inverted (39, 32) Hsaio code providing a Hamming distance of 4.
 *
 * `wr_data_no_intg_i` supplies data that requires integrity calulation and `wr_data_intg_i`
 * supplies data that comes with integrity. `wr_data_intg_sel_i` is asserted to select the data with
 * integrity for the write, otherwise integrity is calculated separately from `wr_data_i`.
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 * - special purpose stack on a single register (localparam `CallStackRegIndex`)
 *   for use as a call stack
 * - triple error detection
 */
module otbn_rf_base
  import otbn_pkg::*;
#(
  // Register file implementation selection, see otbn_pkg.sv.
  parameter regfile_e RegFile = RegFileFF
)(
  input  logic                     clk_i,
  input  logic                     rst_ni,

  input  logic                     state_reset_i,
  input  logic                     sec_wipe_stack_reset_i,

  input  logic [4:0]               wr_addr_i,
  input  logic                     wr_en_i,
  input  logic [31:0]              wr_data_no_intg_i,
  input  logic [BaseIntgWidth-1:0] wr_data_intg_i,
  input  logic                     wr_data_intg_sel_i,
  input  logic                     wr_commit_i,

  input  logic [4:0]               rd_addr_a_i,
  input  logic                     rd_en_a_i,
  output logic [BaseIntgWidth-1:0] rd_data_a_intg_o,

  input  logic [4:0]               rd_addr_b_i,
  input  logic                     rd_en_b_i,
  output logic [BaseIntgWidth-1:0] rd_data_b_intg_o,

  input  logic                     rd_commit_i,

  output logic                     call_stack_sw_err_o,
  output logic                     call_stack_hw_err_o,
  output logic                     intg_err_o,
  output logic                     spurious_we_err_o
);
  localparam int unsigned CallStackRegIndex = 1;
  localparam int unsigned CallStackDepth = 8;

  logic [BaseIntgWidth-1:0] wr_data_intg_mux_out, wr_data_intg_calc;

  logic [BaseIntgWidth-1:0] rd_data_a_raw_intg, rd_data_b_raw_intg;
  logic [1:0]               rd_data_a_err, rd_data_b_err;

  // The stack implementation is shared between FF and FPGA implementations,
  // actual register register file differs between FF and FPGA implementations.
  // Pass through signals to chosen register file, diverting any reads/writes to
  // register CallStatckRegIndex to the stack.

  logic        wr_en_masked;

  logic pop_stack_a;
  logic pop_stack_b;
  logic pop_stack_reqd;
  logic pop_stack;
  logic pop_stack_a_err;
  logic pop_stack_b_err;
  logic push_stack_reqd;
  logic push_stack;
  logic push_stack_err;

  logic                     stack_full;
  logic [BaseIntgWidth-1:0] stack_data_intg;
  logic                     stack_data_valid;

  logic state_reset;

  assign state_reset = state_reset_i | sec_wipe_stack_reset_i;

  assign pop_stack_a     = rd_en_a_i & (rd_addr_a_i == CallStackRegIndex[4:0]);
  assign pop_stack_b     = rd_en_b_i & (rd_addr_b_i == CallStackRegIndex[4:0]);
  // pop_stack_reqd indicates a call stack pop is requested and pop_stack commands it to happen.
  assign pop_stack_reqd  = (pop_stack_a | pop_stack_b);
  assign pop_stack       = rd_commit_i & pop_stack_reqd;
  // Separate error signals for call stack pop for a and b read ports are required to determine if
  // an integrity error is valid or not.
  assign pop_stack_a_err = pop_stack_a & ~stack_data_valid;
  assign pop_stack_b_err = pop_stack_b & ~stack_data_valid;

  // push_stack_reqd indicates a call stack push is requested and push_stack commands it to happen.
  assign push_stack_reqd = wr_en_i & (wr_addr_i == CallStackRegIndex[4:0]);
  assign push_stack      = wr_commit_i & push_stack_reqd;
  // Simultaneous push and pop doesn't cause an error when the stack is full (pop ordered before
  // push).
  assign push_stack_err  = push_stack_reqd & stack_full & ~pop_stack_reqd;

  assign call_stack_sw_err_o = pop_stack_a_err | pop_stack_b_err | push_stack_err;

  // Prevent any write to the stack register from going to the register file,
  // all other committed writes are passed straight through
  assign wr_en_masked = wr_en_i & wr_commit_i & ~push_stack;

  // SEC_CM: CALL_STACK.ADDR.INTEGRITY
  // Ignore read data from the register file if reading from the stack register,
  // otherwise pass data through from register file.
  assign rd_data_a_intg_o = pop_stack_a ? stack_data_intg : rd_data_a_raw_intg;
  assign rd_data_b_intg_o = pop_stack_b ? stack_data_intg : rd_data_b_raw_intg;

  prim_secded_inv_39_32_enc u_wr_data_intg_enc (
    .data_i(wr_data_no_intg_i),
    .data_o(wr_data_intg_calc)
  );

  // New data can have its integrity from an external source or the integrity can be calculated here
  assign wr_data_intg_mux_out = wr_data_intg_sel_i ? wr_data_intg_i : wr_data_intg_calc;

  otbn_stack #(
    // SEC_CM: CALL_STACK.ADDR.INTEGRITY
    .StackWidth(39),
    .StackDepth(CallStackDepth)
  ) u_call_stack (
    .clk_i,
    .rst_ni,

    .full_o        (stack_full),

    .cnt_err_o     (call_stack_hw_err_o),

    .clear_i       (state_reset),

    .push_i        (push_stack),
    .push_data_i   (wr_data_intg_mux_out),

    .pop_i         (pop_stack),
    .top_data_o    (stack_data_intg),
    .top_valid_o   (stack_data_valid),

    .stack_wr_idx_o(),
    .stack_write_o (),
    .stack_rd_idx_o(),
    .stack_read_o  (),

    .next_top_data_o (),
    .next_top_valid_o()
  );

  if (RegFile == RegFileFF) begin : gen_rf_base_ff
    otbn_rf_base_ff #(
      .WordZeroVal(prim_secded_pkg::SecdedInv3932ZeroWord)
    ) u_otbn_rf_base_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i  (wr_en_masked),
      .wr_data_i(wr_data_intg_mux_out),

      .rd_addr_a_i,
      .rd_data_a_o(rd_data_a_raw_intg),
      .rd_addr_b_i,
      .rd_data_b_o(rd_data_b_raw_intg),

      .we_err_o(spurious_we_err_o)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_rf_base_fpga
    otbn_rf_base_fpga #(
      .WordZeroVal(prim_secded_pkg::SecdedInv3932ZeroWord)
    ) u_otbn_rf_base_inner (
      .clk_i,
      .rst_ni,

      .wr_addr_i,
      .wr_en_i  (wr_en_masked),
      .wr_data_i(wr_data_intg_mux_out),

      .rd_addr_a_i,
      .rd_data_a_o(rd_data_a_raw_intg),
      .rd_addr_b_i,
      .rd_data_b_o(rd_data_b_raw_intg),

      .we_err_o(spurious_we_err_o)
    );
  end

  // SEC_CM: RF_BASE.DATA_REG_SW.INTEGRITY
  // Integrity decoders used to detect errors only, corrections (`syndrome_o`/`d_o`) are ignored
  prim_secded_inv_39_32_dec u_rd_data_a_intg_dec (
    .data_i    (rd_data_a_intg_o),
    .data_o    (),
    .syndrome_o(),
    .err_o     (rd_data_a_err)
  );

  prim_secded_inv_39_32_dec u_rd_data_b_intg_dec (
    .data_i    (rd_data_b_intg_o),
    .data_o    (),
    .syndrome_o(),
    .err_o     (rd_data_b_err)
  );

  // Suppress integrity error where the relevant read port saw a call stack pop error (so both
  // integrity and data are invalid).
  assign intg_err_o = (|rd_data_a_err & rd_en_a_i & ~pop_stack_a_err) |
                      (|rd_data_b_err & rd_en_b_i & ~pop_stack_b_err);

  // Make sure we're not outputting X. This indicates that something went wrong during the initial
  // secure wipe.
  `ASSERT(OtbnRfBaseRdAKnown, rd_en_a_i && !pop_stack_a |-> !$isunknown(rd_data_a_raw_intg))
  `ASSERT(OtbnRfBaseRdBKnown, rd_en_b_i && !pop_stack_b |-> !$isunknown(rd_data_b_raw_intg))
endmodule
