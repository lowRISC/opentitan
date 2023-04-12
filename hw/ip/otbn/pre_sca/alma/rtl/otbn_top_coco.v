// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_top_coco #(
  // Instruction data width
  parameter ImemDataWidth = 39,
  // Data path width for BN (wide) instructions, in bits.
  parameter WLEN = 256,
  // Sideload key data width
  parameter SideloadKeyWidth = 384
) (
  input clk_sys,
  input rst_sys_n,
  input imem_we_i,
  input [ImemDataWidth-1:0] imem_wdata_i,
  input [ImemDataWidth-1:0] imem_wmask_i,
  input [WLEN-1:0] edn_rnd_data_i,
  input [WLEN-1:0] edn_urnd_data_i,
  input [SideloadKeyWidth-1:0] sideload_key_share_0_i,
  input [SideloadKeyWidth-1:0] sideload_key_share_1_i,
  output [31:0] otbn_cycle_cnt_o
);
  // Size of the instruction memory, in bytes
  localparam ImemSizeByte = 128*4;  //32'h1000;
  // Size of the data memory, in bytes
  localparam DmemSizeByte = 8*32;  //32'h1000;
  // "Extended" WLEN: the size of the datapath with added integrity bits
  localparam ExtWLEN = WLEN * ImemDataWidth / 32;

  /* Math function: Number of bits needed to address |value| items.
   * This function is taken from prim_util_pkg.sv and re-coded
   *
   *                  0        for value == 0
   * vbits =          1        for value == 1
   *         ceil(log2(value)) for value > 1
   */
  function automatic [31:0] vbits;
    input [31:0] value;
    begin : fclog2
      integer result;
      if (value == 1) begin
        vbits = 1;
      end else begin
        value = value - 1;
        for (result = 0; value > 0; result = result + 1) begin
          value = value >> 1;
        end
        vbits = result;
      end
    end : fclog2
  endfunction

  // Instruction memory adress width
  localparam ImemAddrWidth = vbits(ImemSizeByte);
  // Data memory adress width
  localparam DmemAddrWidth = vbits(DmemSizeByte);

  reg                      otbn_start;
  // Intialise otbn_start_done to 1 so that we only signal otbn_start after we have seen a reset. If
  // you don't do this, we start OTBN before the reset, which can generate confusing trace messages.
  reg                      otbn_start_done = 1'b1;
  wire                     secure_wipe_running;

  // Instruction memory (IMEM) signals
  wire                     imem_req;
  wire [ImemAddrWidth-1:0] imem_addr;
  wire [ImemDataWidth-1:0] imem_rdata;
  wire                     imem_rvalid;

  // Data memory (DMEM) signals
  wire                     dmem_req;
  wire                     dmem_write;
  wire [DmemAddrWidth-1:0] dmem_addr;
  wire [      ExtWLEN-1:0] dmem_wdata;
  wire [      ExtWLEN-1:0] dmem_wmask;
  wire [      ExtWLEN-1:0] dmem_rdata;
  wire                     dmem_rvalid;
  wire                     dmem_rerror;

  // Entropy Distribution Network (EDN)
  wire edn_rnd_req, edn_urnd_req;
  wire edn_rnd_ack, edn_urnd_ack;
  assign edn_rnd_ack  = edn_rnd_req;
  assign edn_urnd_ack = edn_urnd_req;

  // Sideload Key
  wire [2*SideloadKeyWidth-1:0] sideload_key_shares;
  assign sideload_key_shares = {sideload_key_share_1_i, sideload_key_share_0_i};

  localparam [3:0] MuBi4False = 4'h9;

  otbn_core u_otbn_core (
    .clk_i (clk_sys),
    .rst_ni(rst_sys_n),

    .start_i              (otbn_start),
    .done_o               (),
    .locking_o            (),
    .secure_wipe_running_o(secure_wipe_running),

    .err_bits_o       (),
    .recoverable_err_o(),

    .imem_req_o   (imem_req),
    .imem_addr_o  (imem_addr),
    .imem_rdata_i (imem_rdata),
    .imem_rvalid_i(imem_rvalid),

    .dmem_req_o   (dmem_req),
    .dmem_write_o (dmem_write),
    .dmem_addr_o  (dmem_addr),
    .dmem_wdata_o (dmem_wdata),
    .dmem_wmask_o (dmem_wmask),
    .dmem_rmask_o (),
    .dmem_rdata_i (dmem_rdata),
    .dmem_rvalid_i(dmem_rvalid),
    .dmem_rerror_i(dmem_rerror),

    .edn_rnd_req_o (edn_rnd_req),
    .edn_rnd_ack_i (edn_rnd_ack),
    .edn_rnd_data_i(edn_rnd_data_i),
    .edn_rnd_fips_i(1'b1),
    .edn_rnd_err_i (1'b0),

    .edn_urnd_req_o (edn_urnd_req),
    .edn_urnd_ack_i (edn_urnd_ack),
    .edn_urnd_data_i(edn_urnd_data_i),

    .insn_cnt_o      (),
    .insn_cnt_clear_i(1'b0),

    .mems_sec_wipe_o         (),
    .dmem_sec_wipe_urnd_key_o(),
    .imem_sec_wipe_urnd_key_o(),
    .req_sec_wipe_urnd_keys_i(1'b0),

    .escalate_en_i(MuBi4False),
    .rma_req_i    (MuBi4False),
    .rma_ack_o    (),

    .software_errs_fatal_i(1'b0),

    .sideload_key_shares_i      (sideload_key_shares),
    .sideload_key_shares_valid_i(2'b11)
  );

  // Track when OTBN is done with its initial secure wipe of the internal state.  We use this to
  // wait for the OTBN core to complete the initial secure wipe before we send it the start signal.
  // Also keep a delayed copy of the done signal.  This is necessary to align with the status of
  // OTBN and the model, which lags one cycle behind the completion of the OTBN core.
  reg init_sec_wipe_done_q;
  always @(posedge clk_sys, negedge rst_sys_n) begin
    if (!rst_sys_n) begin
      init_sec_wipe_done_q <= 1'b0;
    end else begin
      if (!secure_wipe_running) begin
        init_sec_wipe_done_q <= 1'b1;
      end
    end
  end

  // Pulse otbn_start for 1 cycle after the initial secure wipe is done.
  // Flop `done_o` from otbn_core to match up with model done signal.
  always @(posedge clk_sys or negedge rst_sys_n) begin
    if (!rst_sys_n) begin
      otbn_start      <= 1'b0;
      otbn_start_done <= 1'b0;
    end else begin
      if (!otbn_start_done && init_sec_wipe_done_q) begin
        otbn_start      <= 1'b1;
        otbn_start_done <= 1'b1;
      end else if (otbn_start) begin
        otbn_start <= 1'b0;
      end
    end
  end

  // OTBN cycle counter to easily inspect waves and associate those waves with COCO-ALMA tool
  // output. The counter is reset with the start pulse being sent.
  reg [31:0] otbn_cycle_cnt_q;
  always @(posedge clk_sys or negedge rst_sys_n) begin
    if (!rst_sys_n) begin
      otbn_cycle_cnt_q <= 32'b0;
    end else begin
      if (otbn_start) begin
        otbn_cycle_cnt_q <= 32'b0;
      end else if (otbn_start_done) begin
        otbn_cycle_cnt_q <= otbn_cycle_cnt_q + 1;
      end
    end
  end
  assign otbn_cycle_cnt_o = otbn_cycle_cnt_q;

  localparam DmemSizeWords = DmemSizeByte / (WLEN / 8);
  localparam DmemIndexWidth = vbits(DmemSizeWords);

  wire [DmemIndexWidth-1:0] dmem_index;
  wire [DmemAddrWidth-DmemIndexWidth-1:0] unused_dmem_addr;

  assign dmem_index = dmem_addr[DmemAddrWidth-1:DmemAddrWidth-DmemIndexWidth];
  assign unused_dmem_addr = dmem_addr[DmemAddrWidth-DmemIndexWidth-1:0];

  assign dmem_rerror = 1'b0;

  ram_1p #(
    .DataWidth(ExtWLEN),
    .AddrWidth(DmemIndexWidth),
    .Depth(DmemSizeWords)
  ) u_dmem (
    .clk_i(clk_sys),
    .rst_ni(rst_sys_n),
    .req_i(dmem_req),
    .we_i(dmem_write),
    .addr_i(dmem_index),
    .wdata_i(dmem_wdata),
    .wmask_i(dmem_wmask),
    .rvalid_o(dmem_rvalid),
    .rdata_o(dmem_rdata)
  );

  localparam ImemSizeWords = ImemSizeByte / 4;
  localparam ImemIndexWidth = vbits(ImemSizeWords);

  wire [ImemIndexWidth-1:0] imem_index;
  wire [1:0] unused_imem_addr;

  assign imem_index = imem_addr[ImemAddrWidth-1:2];
  assign unused_imem_addr = imem_addr[1:0];

  ram_1p #(
    .DataWidth(ImemDataWidth),
    .AddrWidth(ImemIndexWidth),
    .Depth(ImemSizeWords)
  ) u_imem (
    .clk_i(clk_sys),
    .rst_ni(rst_sys_n),
    .req_i(imem_req),
    .we_i(imem_we_i),
    .addr_i(imem_index),
    .wdata_i(imem_wdata_i),
    .wmask_i(imem_wmask_i),
    .rvalid_o(imem_rvalid),
    .rdata_o(imem_rdata)
  );

endmodule
