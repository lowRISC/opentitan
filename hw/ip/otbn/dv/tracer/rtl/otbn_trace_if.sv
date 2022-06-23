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
  parameter int ImemAddrWidth = 12,
  parameter int DmemAddrWidth = 12,
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
  input logic rf_base_wr_commit,

  input logic [otbn_pkg::WdrAw-1:0] rf_bignum_rd_addr_a,
  input logic [otbn_pkg::WdrAw-1:0] rf_bignum_rd_addr_b,
  input logic [otbn_pkg::WdrAw-1:0] rf_bignum_wr_addr,

  input logic                      rf_bignum_rd_en_a,
  input logic                      rf_bignum_rd_en_b,

  input logic [1:0]                   rf_bignum_wr_en,
  input logic                         rf_bignum_wr_commit,
  input logic [otbn_pkg::WLEN-1:0]    rf_bignum_wr_data_no_intg,
  input logic [otbn_pkg::ExtWLEN-1:0] rf_bignum_wr_data_intg,
  input logic                         rf_bignum_wr_data_intg_sel,

  input logic [31:0]              insn_fetch_resp_data,
  input logic [ImemAddrWidth-1:0] insn_fetch_resp_addr,
  input logic                     insn_fetch_resp_valid,
  input logic                     insn_fetch_err,

  input logic                         dmem_req_o,
  input logic                         dmem_write_o,
  input logic [DmemAddrWidth-1:0]     dmem_addr_o,
  input logic [otbn_pkg::ExtWLEN-1:0] dmem_wdata_o,
  input logic [otbn_pkg::ExtWLEN-1:0] dmem_wmask_o,
  input logic [otbn_pkg::ExtWLEN-1:0] dmem_rdata_i,

  input otbn_pkg::ispr_e                 ispr_addr,
  input logic                            ispr_init,
  input otbn_pkg::insn_dec_shared_t      insn_dec_shared,
  input otbn_pkg::insn_dec_bignum_t      insn_dec_bignum,
  input otbn_pkg::alu_bignum_operation_t alu_bignum_operation,
  input logic                            mac_bignum_en,

  input logic [otbn_pkg::WLEN-1:0] rnd_data,
  input logic                      rnd_req,
  input logic                      rnd_valid,

  input logic [otbn_pkg::WLEN-1:0] urnd_data,

  input logic [1:0][otbn_pkg::SideloadKeyWidth-1:0] sideload_key_shares_i,

  input logic secure_wipe_req,
  input logic secure_wipe_ack
);
  import otbn_pkg::*;

  localparam int DmemSubWordAddrWidth = prim_util_pkg::vbits(WLEN/8);

  // `insn_stall` isn't a signal that exists in the design so needs creating here. To keep things
  // consistent `insn_X` signals are provided here that are simply assigned to `otbn_core` signals.
  // To prevent the tracer needing to deal with differing Imem sizes the address is padded out to
  // 32-bits.
  logic        insn_valid;
  logic [31:0] insn_addr;
  logic [31:0] insn_data;
  logic        insn_stall;

  assign insn_valid     = insn_fetch_resp_valid;
  assign insn_addr      = {{(32-ImemAddrWidth){1'b0}}, insn_fetch_resp_addr};
  assign insn_data      = insn_fetch_resp_data;
  assign insn_stall     = u_otbn_core.u_otbn_controller.state_d == OtbnStateStall;

  logic [31:0] rf_base_rd_data_a;
  logic [31:0] rf_base_rd_data_b;
  logic [31:0] rf_base_wr_data;

  logic [WLEN-1:0] rf_bignum_rd_data_a;
  logic [WLEN-1:0] rf_bignum_rd_data_b;

  assign rf_base_rd_data_a = u_otbn_controller.rf_base_rd_data_a_no_intg;
  assign rf_base_rd_data_b = u_otbn_controller.rf_base_rd_data_b_no_intg;
  assign rf_base_wr_data = u_otbn_rf_base.wr_data_intg_mux_out[31:0];

  assign rf_bignum_rd_data_a = u_otbn_controller.rf_bignum_rd_data_a_no_intg;
  assign rf_bignum_rd_data_b = u_otbn_controller.rf_bignum_rd_data_b_no_intg;

  // The bignum register file is capable of half register writes. To avoid the tracer having to deal
  // with this, it should just OR together the bits of rf_bignum_wr_en to get a single "there was a
  // write" signal.
  //
  // We also clean up the (complicated) write data signals here and present them as
  // rf_bignum_wr_data. Integrity is stripped. If there is a half-word write then the other half of
  // the register is taken directly from the register file and both halves are presented as the
  // write data to the tracer.
  logic [WLEN-1:0] rf_bignum_wr_data;
  logic [WLEN-1:0] rf_bignum_wr_data_stripped_intg, rf_bignum_wr_new_data, rf_bignum_wr_old_data;
  logic [BaseWordsPerWLEN-1:0] unused_bignum_intg_data;

  logic [ExtWLEN-1:0] bignum_rf [NWdr];

  for (genvar i = 0; i < NWdr; ++i) begin : g_probe_bignum_rf
    if (RegFile == RegFileFF) begin : g_rf_ff_probe
      assign bignum_rf[i] = u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf[i];
    end else if (RegFile == RegFileFPGA) begin : g_rf_fpga_probe
      assign bignum_rf[i] = u_otbn_rf_bignum.gen_rf_bignum_fpga.u_otbn_rf_bignum_inner.rf[i];
    end
  end

  for (genvar i = 0; i < BaseWordsPerWLEN; ++i) begin : g_bignum_rf_strip_intg
    // Strip out integrity bits from rf_bignum_wr_data_intg so that we can use this as a source for
    // rf_bignum_wr_data_for_trace when rf_bignum_wr_data_intg_sel is set.
    assign rf_bignum_wr_data_stripped_intg[i*32 +: 32] =
        rf_bignum_wr_data_intg[i * BaseIntgWidth +: 32];

    // Extract data currently in the register file for the current write address, stripping off
    // integrity. This is used to determine the final value for the whole register when doing half
    // register writes.
    assign rf_bignum_wr_old_data[i*32 +: 32] =
        bignum_rf[rf_bignum_wr_addr][i * BaseIntgWidth +: 32];

    // Explicitly ignore the integrity bits
    assign unused_bignum_intg_data[i] =
        ^rf_bignum_wr_data_intg[i*BaseIntgWidth+32 +: (BaseIntgWidth - 32)];
  end

  // Use the intg_sel signal to pick where the new write data should come from
  assign rf_bignum_wr_new_data =
      rf_bignum_wr_data_intg_sel ? rf_bignum_wr_data_stripped_intg : rf_bignum_wr_data_no_intg;

  for (genvar i = 0; i < 2; i++) begin : g_rf_bignum_wr_data
    // Use the write-enable signal to pick whether to use new data or old.
    assign rf_bignum_wr_data[(WLEN/2)*i +: WLEN/2] =
        rf_bignum_wr_en[i] ?
        rf_bignum_wr_new_data[(WLEN/2)*i +: WLEN/2] :
        rf_bignum_wr_old_data[(WLEN/2)*i +: WLEN/2];
  end

  // Take Dmem interface and present it as two separate read and write sets of signals. To ease
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

  // Remove interleaved integrity bits from memory read and write data
  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_mem_strip_intg
    logic unused_intg;

    assign dmem_write_data[i_word*32 +: 32] = dmem_wdata_o[i_word*BaseIntgWidth +: 32];
    assign dmem_write_mask[i_word*32 +: 32] = dmem_wmask_o[i_word*BaseIntgWidth +: 32];
    assign dmem_read_data [i_word*32 +: 32] = dmem_rdata_i[i_word*BaseIntgWidth +: 32];

    assign unused_intg = (|dmem_wdata_o[i_word*BaseIntgWidth+32 +: BaseIntgWidth-32]) |
      (|dmem_wmask_o[i_word* BaseIntgWidth+32 +: BaseIntgWidth-32]) |
      (|dmem_rdata_i[i_word* BaseIntgWidth+32 +: BaseIntgWidth-32]);
  end

  // TODO: Tracing for read errors

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
  // useful to present those differently so separate signals are provided for the tracing of them.
  logic [NIspr-1:0] ispr_write;
  logic [WLEN-1:0]  ispr_write_data [NIspr];
  logic [NIspr-1:0] ispr_read;
  logic [WLEN-1:0]  ispr_read_data [NIspr];

  logic any_ispr_read;

  assign any_ispr_read =
      (insn_dec_shared.ispr_rd_insn | insn_dec_shared.ispr_rs_insn) & insn_fetch_resp_valid;


  assign ispr_write[IsprMod] = |u_otbn_alu_bignum.mod_wr_en & ~ispr_init;

  for (genvar i_word = 0; i_word < BaseWordsPerWLEN; i_word++) begin : g_mod_and_acc_words
    assign ispr_write_data[IsprMod][i_word*32+:32] =
      u_otbn_alu_bignum.mod_wr_en[i_word] ? u_otbn_alu_bignum.mod_intg_d[i_word*39+:32] :
                                            u_otbn_alu_bignum.mod_intg_q[i_word*39+:32];
    assign ispr_read_data[IsprMod][i_word*32+:32] = u_otbn_alu_bignum.mod_intg_q[i_word*39+:32];
    assign ispr_write_data[IsprAcc][i_word*32+:32] = u_otbn_mac_bignum.acc_intg_d[i_word*39+:32];
  end

  assign ispr_read[IsprMod] =
    (any_ispr_read & (ispr_addr == IsprMod)) |
    (insn_fetch_resp_valid &
     (alu_bignum_operation.op inside {AluOpBignumAddm, AluOpBignumSubm}));

  assign ispr_write[IsprAcc] = u_otbn_mac_bignum.acc_en & ~ispr_init;

  assign ispr_read[IsprAcc] = (any_ispr_read & (ispr_addr == IsprAcc)) | mac_bignum_en;
  // For ISPR reads look at the ACC flops directly. For other ACC reads look at the `acc_blanked`
  // signal in order to read ACC as 0 for the BN.MULQACC.Z instruction variant.
  assign ispr_read_data[IsprAcc] =
      (any_ispr_read & (ispr_addr == IsprAcc)) ? u_otbn_mac_bignum.acc_no_intg_q  :
                                                 u_otbn_mac_bignum.acc_blanked;

  assign ispr_write[IsprRnd] = 1'b0;
  assign ispr_write_data[IsprRnd] = '0;
  assign ispr_write[IsprUrnd] = 1'b0;
  assign ispr_write_data[IsprUrnd] = '0;

  assign ispr_read[IsprRnd] = any_ispr_read & (ispr_addr == IsprRnd) & rnd_req & rnd_valid;
  assign ispr_read_data[IsprRnd] = rnd_data;

  assign ispr_read[IsprUrnd] = any_ispr_read & (ispr_addr == IsprUrnd);
  assign ispr_read_data[IsprUrnd] = urnd_data;

  assign ispr_write[IsprKeyS0L] = 1'b0;
  assign ispr_write_data[IsprKeyS0L] = '0;
  assign ispr_write[IsprKeyS0H] = 1'b0;
  assign ispr_write_data[IsprKeyS0H] = '0;
  assign ispr_write[IsprKeyS1L] = 1'b0;
  assign ispr_write_data[IsprKeyS1L] = '0;
  assign ispr_write[IsprKeyS1H] = 1'b0;
  assign ispr_write_data[IsprKeyS1H] = '0;

  assign ispr_read[IsprKeyS0L] = any_ispr_read & (ispr_addr == IsprKeyS0L);
  assign ispr_read_data[IsprKeyS0L] = sideload_key_shares_i[0][255:0];

  assign ispr_read[IsprKeyS0H] = any_ispr_read & (ispr_addr == IsprKeyS0H);
  assign ispr_read_data[IsprKeyS0H] = {{(WLEN - (SideloadKeyWidth - 256)){1'b0}},
                                       sideload_key_shares_i[0][SideloadKeyWidth-1:256]};

  assign ispr_read[IsprKeyS1L] = any_ispr_read & (ispr_addr == IsprKeyS0L);
  assign ispr_read_data[IsprKeyS1L] = sideload_key_shares_i[1][255:0];

  assign ispr_read[IsprKeyS1H] = any_ispr_read & (ispr_addr == IsprKeyS1H);
  assign ispr_read_data[IsprKeyS1H] = {{(WLEN - (SideloadKeyWidth - 256)){1'b0}},
                                       sideload_key_shares_i[1][SideloadKeyWidth-1:256]};

  // Separate per flag group tracking using the flags_t struct so tracer can cleanly present flag
  // accesses.
  logic [NFlagGroups-1:0] flags_write;
  flags_t                 flags_write_data [NFlagGroups];
  logic [NFlagGroups-1:0] flags_read;
  flags_t                 flags_read_data [NFlagGroups];
  logic                   flag_group_read_op;

  // Determine if current instruction reads a flag group specified in the instruction.
  assign flag_group_read_op =
      alu_bignum_operation.mac_flag_en                                                  |
      insn_dec_bignum.sel_insn                                                          |
      (alu_bignum_operation.op inside {AluOpBignumAddc, AluOpBignumSubb, AluOpBignumXor,
                                       AluOpBignumOr, AluOpBignumAnd, AluOpBignumNot});

  for (genvar i_fg = 0; i_fg < NFlagGroups; i_fg++) begin : g_flag_group_acceses
    assign flags_write[i_fg] = u_otbn_alu_bignum.flags_en[i_fg] & ~ispr_init;
    assign flags_write_data[i_fg] = u_otbn_alu_bignum.flags_d[i_fg];

    assign flags_read[i_fg] = (any_ispr_read & (ispr_addr == IsprFlags)) |
         (flag_group_read_op & (alu_bignum_operation.flag_group == i_fg) & insn_fetch_resp_valid);

    assign flags_read_data[i_fg] = u_otbn_alu_bignum.flags_q[i_fg];
  end

  logic initial_secure_wipe_done;
  logic secure_wipe_ack_r;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      initial_secure_wipe_done <= 1'b0;
      secure_wipe_ack_r <= 1'b0;
    end else begin
      secure_wipe_ack_r <= secure_wipe_ack;
      if (secure_wipe_ack) begin
        initial_secure_wipe_done <= 1'b1;
      end
    end
  end

endinterface

`endif // SYNTHESIS
