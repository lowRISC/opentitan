// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SYNTHESIS

/**
 * Interface designed to be bound into otbn_core and extract out signals useful for the tracer.
 *
 * The tracer takes an instance of this interface as one of its module ports. The tracer will
 * examine both inputs to this interface as well as signals created within it. This interface is
 * quite messy, it is built following the principles below that lead to its current design:
 *
 * 1. Producing suitable signals for a tracer from internal design signals can be a messy/fiddly
 *    process. Anything that is messy/fiddly should be confined to this file if at all possible so
 *    the tracer itself can be cleanly written.
 * 2. Aim to provide signals from interface to the tracer with clear consistent naming, this may
 *    result in situations where this interface simply renames an existing otbn_core signal (by
 *    bringing it in via an input and then assigning it to an internal signal).
 * 3. Hierarchical references can only refer to modules inside otbn_core, not otbn_core itself as
 *    this requires assuming the instance name of otbn_core (which could vary from environment to
 *    environment).
 * 4. To use a signal from the otbn_core module, name it as an input with the name used in
 *    otbn_core.  Whatever binds the interface into otbn_core is responsible for connecting these
 *    up, e.g. using a wildcard '.*'.
 */
interface otbn_trace_if
#(
  parameter int ImemAddrWidth,
  parameter int DmemAddrWidth,
  parameter otbn_pkg::regfile_e RegFile = otbn_pkg::RegFileFF
)(
  input logic clk_i,
  input logic rst_ni,

  input logic [4:0] rf_base_rd_addr_a,
  input logic [4:0] rf_base_rd_addr_b,
  input logic [4:0] rf_base_wr_addr,

  input logic rf_base_rd_en_a,
  input logic rf_base_rd_en_b,
  input logic rf_base_wr_en,

  input logic [31:0] rf_base_rd_data_a,
  input logic [31:0] rf_base_rd_data_b,
  input logic [31:0] rf_base_wr_data,

  input logic [otbn_pkg::WdrAw-1:0] rf_bignum_rd_addr_a,
  input logic [otbn_pkg::WdrAw-1:0] rf_bignum_rd_addr_b,
  input logic [otbn_pkg::WdrAw-1:0] rf_bignum_wr_addr,

  input logic [otbn_pkg::WLEN-1:0] rf_bignum_rd_data_a,
  input logic [otbn_pkg::WLEN-1:0] rf_bignum_rd_data_b,

  input logic [31:0]              insn_fetch_resp_data,
  input logic [ImemAddrWidth-1:0] insn_fetch_resp_addr,
  input logic                     insn_fetch_resp_valid,

  input logic                      dmem_req_o,
  input logic                      dmem_write_o,
  input logic [DmemAddrWidth-1:0]  dmem_addr_o,
  input logic [otbn_pkg::WLEN-1:0] dmem_wdata_o,
  input logic [otbn_pkg::WLEN-1:0] dmem_wmask_o,
  input logic [otbn_pkg::WLEN-1:0] dmem_rdata_i,

  input otbn_pkg::ispr_e                 ispr_addr,
  input otbn_pkg::insn_dec_shared_t      insn_dec_shared,
  input otbn_pkg::alu_bignum_operation_t alu_bignum_operation,
  input logic                            mac_bignum_en,

  input logic [otbn_pkg::WLEN-1:0] rnd
);
  import otbn_pkg::*;

  localparam int DmemSubWordAddrWidth = prim_util_pkg::vbits(WLEN/8);

  logic rf_ren_a_bignum;
  logic rf_ren_b_bignum;

  // Read enables for bignum are only inside the decoder with the current design, so bring them out
  // here for access by the tracer.
  assign rf_ren_a_bignum = u_otbn_decoder.rf_ren_a_bignum;
  assign rf_ren_b_bignum = u_otbn_decoder.rf_ren_b_bignum;

  // The bignum register file is capable of half register writes. To avoid the tracer having to deal
  // with this, slightly modified rf_bignum_wr_en and rf_bignum_wr_data signals are provided here.
  // If there is a half-word write the other half of the register is taken directly from the
  // register file and both halves are presented as the write data to the tracer. `rf_bignum_wr_en`
  // becomes a single bit signal because of this.
  logic            rf_bignum_wr_en;
  logic [WLEN-1:0] rf_bignum_wr_data;

  assign rf_bignum_wr_en = |u_otbn_controller.rf_bignum_wr_en_o;

  logic [WLEN-1:0] rf_bignum_wr_old_data;

  if (RegFile == RegFileFF) begin : g_rf_ff_bignum_wr_old_data
    assign rf_bignum_wr_old_data = gen_rf_bignum_ff.u_otbn_rf_bignum.rf[rf_bignum_wr_addr];
  end else if (RegFile == RegFileFPGA) begin : g_rf_fpga_bignum_wr_old_data
    assign rf_bignum_wr_old_data = gen_rf_bignum_fpga.u_otbn_rf_bignum.rf[rf_bignum_wr_addr];
  end

  for (genvar i = 0; i < 2; i++) begin : g_rf_bignum_wr_data
    assign rf_bignum_wr_data[(WLEN/2)*i +: WLEN/2] = u_otbn_controller.rf_bignum_wr_en_o[i] ?
      u_otbn_controller.rf_bignum_wr_data_o[(WLEN/2)*i +: WLEN/2] :
      rf_bignum_wr_old_data[(WLEN/2)*i +: WLEN/2];
  end

  // `insn_stall` isn't a signal that exists in the design so needs creating here. To keep things
  // consistent `insn_X` signals are provided here that are simply assigned to `otbn_core` signals.
  // To prevent the tracer needing to deal with differing Imem sizes the address is padded out to
  // 32-bits.
  logic        insn_valid;
  logic [31:0] insn_addr;
  logic [31:0] insn_data;
  logic        insn_stall;

  assign insn_valid = insn_fetch_resp_valid;
  assign insn_addr  = {{(32-ImemAddrWidth){1'b0}}, insn_fetch_resp_addr};
  assign insn_data  = insn_fetch_resp_data;
  assign insn_stall = u_otbn_core.u_otbn_controller.state_d == OtbnStateStall;

  // Take Dmem interface and present it as two seperate read and write sets of signals. To ease
  // tracer implementation a small tracker tracks reads so the whole transaction (address + data
  // together) is presented in a single cycle.
  logic [31:0]     dmem_wlen_aligned_addr;

  logic            dmem_write;
  logic [31:0]     dmem_write_addr;
  logic [WLEN-1:0] dmem_write_data;
  logic [WLEN-1:0] dmem_write_mask;

  logic            dmem_read;
  logic [31:0]     dmem_read_addr;
  logic [WLEN-1:0] dmem_read_data;

  assign dmem_wlen_aligned_addr = {{(32-DmemAddrWidth){1'b0}},
                                   dmem_addr_o[DmemAddrWidth-1:DmemSubWordAddrWidth],
                                   {DmemSubWordAddrWidth{1'b0}}};
  assign dmem_write      = dmem_req_o & dmem_write_o;
  assign dmem_write_addr = dmem_wlen_aligned_addr;

  assign dmem_write_data = dmem_wdata_o;
  assign dmem_write_mask = dmem_wmask_o;

  // TODO: Tracing for read errors
  assign dmem_read_data  = dmem_rdata_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dmem_read      <= 1'b0;
      dmem_read_addr <= '0;
    end else begin
      dmem_read      <= dmem_req_o & ~dmem_write_o;
      dmem_read_addr <= dmem_wlen_aligned_addr;
    end
  end

  // ISPRs all have slightly different implementations and each have their own specific read/write
  // sources. This presents a uniform interface for all ispr reads/writes, excluding flags, as it's
  // useful to present those differently so seperate signals are provided for the tracing of them.
  logic [NIspr-1:0] ispr_write;
  logic [WLEN-1:0]  ispr_write_data [NIspr];
  logic [NIspr-1:0] ispr_read;
  logic [WLEN-1:0]  ispr_read_data [NIspr];

  logic any_ispr_read;

  assign any_ispr_read =
      (insn_dec_shared.ispr_rd_insn | insn_dec_shared.ispr_rs_insn) & insn_fetch_resp_valid;


  assign ispr_write[IsprMod] = |u_otbn_alu_bignum.mod_wr_en;

  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_mod_words
    assign ispr_write_data[IsprMod][i_word*32+:32] =
      u_otbn_alu_bignum.mod_wr_en[i_word] ? u_otbn_alu_bignum.mod_d[i_word*32+:32] :
                                            u_otbn_alu_bignum.mod_q[i_word*32+:32];
  end

  assign ispr_read[IsprMod] = (any_ispr_read & (ispr_addr == IsprMod)) |
    (alu_bignum_operation.op inside {AluOpBignumAddm, AluOpBignumSubm});

  assign ispr_read_data[IsprMod] = u_otbn_alu_bignum.mod_q;

  assign ispr_write[IsprAcc] = u_otbn_mac_bignum.acc_en;
  assign ispr_write_data[IsprAcc] = u_otbn_mac_bignum.acc_d;

  assign ispr_read[IsprAcc] = (any_ispr_read & (ispr_addr == IsprAcc)) | mac_bignum_en;
  // For ISPR reads look at the ACC flops directly. For other ACC reads look at the `acc` signal in
  // order to read ACC as 0 for the BN.MULQACC.Z instruction variant.
  assign ispr_read_data[IsprAcc] =
      (any_ispr_read & (ispr_addr == IsprAcc)) ? u_otbn_mac_bignum.acc_q : u_otbn_mac_bignum.acc;

  assign ispr_write[IsprRnd] = 1'b0;
  assign ispr_write_data[IsprRnd] = '0;

  assign ispr_read[IsprRnd] = any_ispr_read & (ispr_addr == IsprRnd);
  assign ispr_read_data[IsprRnd] = rnd;

  // Seperate per flag group tracking using the flags_t struct so tracer can cleanly present flag
  // accesses.
  logic [NFlagGroups-1:0] flags_write;
  flags_t                 flags_write_data [NFlagGroups];
  logic [NFlagGroups-1:0] flags_read;
  flags_t                 flags_read_data [NFlagGroups];
  logic                   flag_group_read_op;

  // Determine if current instruction reads a flag group specified in the instruction.
  assign flag_group_read_op =
      alu_bignum_operation.mac_flag_en                                                  |
      (alu_bignum_operation.op inside {AluOpBignumAddc, AluOpBignumSubb, AluOpBignumSel,
                                       AluOpBignumXor, AluOpBignumOr, AluOpBignumAnd,
                                       AluOpBignumNot});

  for (genvar i_fg = 0; i_fg < NFlagGroups; i_fg++) begin : g_flag_group_acceses
    assign flags_write[i_fg] = u_otbn_alu_bignum.flags_en[i_fg];
    assign flags_write_data[i_fg] = u_otbn_alu_bignum.flags_d[i_fg];

    assign flags_read[i_fg] = (any_ispr_read & (ispr_addr == IsprFlags)) |
         (flag_group_read_op & (alu_bignum_operation.flag_group == i_fg) & insn_fetch_resp_valid);

    assign flags_read_data[i_fg] = u_otbn_alu_bignum.flags_q[i_fg];
  end
endinterface

`endif // SYNTHESIS
