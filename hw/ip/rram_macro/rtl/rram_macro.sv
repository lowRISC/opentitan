// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Open-source RRAM macro
//
// This module emulates the real RRAM macro with a simple FSM and two prim_ram_1p for data and info
// arrays.
// Operations have random execution time which is achieved with a LFSR and a cycle counter.

module rram_macro #(
  parameter int unsigned TotalDataPages = 4096, // Total number of data pages
  parameter int unsigned DataWidth      = 128,  // RRAM word data width
  parameter int unsigned WordsPerPage   = 32,   // Number of words per page
  parameter int unsigned TotalInfoPages = 8,    // Total number of info pages
  parameter int unsigned MaxWrWords     = 32    // Maximum number of words per write
) (
  input logic                            clk_i,
  input logic                            rst_ni,
  // Functional connections
  input rram_ctrl_pkg::rram_macro_req_t  rram_macro_i,
  output rram_ctrl_pkg::rram_macro_rsp_t rram_macro_o,
  input tlul_pkg::tl_h2d_t               prim_tl_i,
  output tlul_pkg::tl_d2h_t              prim_tl_o,
  // Test connections
  input logic                  cio_tck_i,
  input logic                  cio_tdi_i,
  input logic                  cio_tms_i,
  output logic                 cio_tdo_o,
  output logic                 cio_tdo_en_o,
  input lc_ctrl_pkg::lc_tx_t   lc_nvm_debug_en_i,
  input prim_mubi_pkg::mubi4_t scanmode_i,
  input logic                  scan_en_i,
  input logic                  scan_rst_ni,
  inout wire                   rram_test_analog_io,
  // Observability
  input ast_pkg::ast_obs_ctrl_t obs_ctrl_i,
  output logic [7:0]            rram_obs_o
);

  import rram_macro_reg_pkg::*;
  import rram_ctrl_pkg::*;

  ///////////////////////////////////////
  // Unused ports in open-source model //
  ///////////////////////////////////////
  logic unused_scanmode;
  logic unused_scan_en;
  logic unused_scan_rst_n;
  logic unused_rram_test_analog;
  logic unused_tck;
  logic unused_tdi;
  logic unused_tms;

  lc_ctrl_pkg::lc_tx_t unused_lc_nvm_debug_en;

  assign unused_scanmode   = ^scanmode_i;
  assign unused_scan_en    = scan_en_i;
  assign unused_scan_rst_n = scan_rst_ni;

  assign unused_rram_test_analog = rram_test_analog_io;

  assign unused_lc_nvm_debug_en = lc_nvm_debug_en_i;

  assign unused_tck   = cio_tck_i;
  assign unused_tdi   = cio_tdi_i;
  assign unused_tms   = cio_tms_i;
  assign cio_tdo_o    = '0;
  assign cio_tdo_en_o = '0;

  ////////////////////////////////////
  // TL-UL Test Interface Emulation //
  ////////////////////////////////////

  logic intg_err, fsm_err;
  rram_macro_reg_pkg::rram_macro_prim_reg2hw_t reg2hw;
  rram_macro_reg_pkg::rram_macro_prim_hw2reg_t hw2reg;
  rram_macro_prim_reg_top u_reg_prim (
    .clk_i,
    .rst_ni,
    .tl_i      (prim_tl_i),
    .tl_o      (prim_tl_o),
    .reg2hw    (reg2hw),
    .hw2reg    (hw2reg),
    .intg_err_o(intg_err)
  );

  logic unused_reg_sig;
  assign unused_reg_sig = ^reg2hw;
  assign hw2reg         = '0;

  assign rram_macro_o.fatal_err = intg_err | fsm_err;
  assign rram_macro_o.recov_err = 1'b0;

  logic unused_obs;
  assign unused_obs = |obs_ctrl_i;

  /////////////////////////////////////
  // open-source RRAM implementation //
  /////////////////////////////////////

  // ECC parameters: the RRAM word is protected with 2x64b Hamming(72,64) SECDED codes.
  localparam int unsigned EccNumWords   = 2;
  localparam int unsigned EccWordWidth  = 64;
  localparam int unsigned EccCodeWidth  = 72;
  localparam int unsigned EccCheckWidth = EccCodeWidth - EccWordWidth; // 8: check bits per half
  localparam int unsigned FullDataWidth = EccNumWords * EccCodeWidth; // 144: physical storage width

  `ASSERT_INIT(RramMacroFullDataWidth_A, DataWidth == EccNumWords * EccWordWidth)

  localparam int StoreBufWidth  = FullDataWidth + prim_util_pkg::vbits(WordsPerPage);

  localparam int DataAddrW = prim_util_pkg::vbits(TotalDataPages * WordsPerPage);
  localparam int InfoAddrW = prim_util_pkg::vbits(TotalInfoPages * WordsPerPage);

  // Latencies of the individual operations in clock cycles (to be refined later)
  localparam int InitLatency     = 10000;
  localparam int ReadLatency     = 3;
  localparam int WriteLatency    = 1000;
  localparam int StoreBufLatency = 2;

  // Encoding generated at commit 0eeae81c80 using Python 3.12.13 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 450951119 --distance 5 --states 8 --bits 10
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (42.86%)
  //  6: |||||||||||||||||||| (42.86%)
  //  7: |||||| (14.29%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StReset    = 10'b1001111000,
    StInit     = 10'b0000111111,
    StIdle     = 10'b0010001010,
    StRead     = 10'b0100010000,
    StStoreBuf = 10'b1110001101,
    StWrite    = 10'b1101100011,
    StRetErr   = 10'b1011010111,
    StErr      = 10'b0111100100
  } state_e;

  state_e state_d, state_q;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StReset)

  // auxiliary counters
  logic [31:0] cnt_q;
  logic        cnt_inc, cnt_clr;

  rram_part_e           current_part_q, current_part_d;
  logic [DataAddrW-1:0] waddr_q, waddr_d;
  logic                 ecc_en_q, ecc_en_d;

  // store_buf_fifo signals
  logic                      store_buf_fifo_wvalid;
  logic [StoreBufWidth-1:0]  store_buf_fifo_wdata;
  logic                      store_buf_fifo_full;
  logic                      store_buf_fifo_rvalid;
  logic                      store_buf_fifo_rready;
  logic [WordW-1:0]          store_buf_fifo_offset;
  logic [FullDataWidth-1:0]  store_buf_fifo_data;

  logic                     mem_req;
  logic                     mem_wr;
  logic [DataAddrW-1:0]     mem_addr;
  logic [FullDataWidth-1:0] mem_wdata;
  logic [FullDataWidth-1:0] mem_rdata;
  logic [FullDataWidth-1:0] mem_rdata_q;
  logic                     mem_rvalid_d, mem_rvalid_q;

  logic                     data_mem_req;
  logic                     data_mem_wr;
  logic [DataAddrW-1:0]     data_mem_addr;
  logic [FullDataWidth-1:0] data_mem_wdata;
  logic [FullDataWidth-1:0] data_mem_rdata;

  logic                     info_mem_req;
  logic                     info_mem_wr;
  logic [InfoAddrW-1:0]     info_mem_addr;
  logic [FullDataWidth-1:0] info_mem_wdata;
  logic [FullDataWidth-1:0] info_mem_rdata;

  logic                 done;
  logic                 ack;
  logic [DataWidth-1:0] rdata;
  logic                 err;
  logic [2:0]           ecc_err;
  logic                 init_done;

  // ECC encode path (write): computed before data enters u_store_buf_fifo. Physical layout is
  // {ecc1, ecc0, data1, data0}: both check-bit bytes grouped at the MSBs, with the two 64b data
  // halves unchanged and contiguous below (matching rram_macro_i.wr_data exactly) at the LSBs.
  logic [EccWordWidth-1:0]  wr_data_lo, wr_data_hi;
  logic [EccCodeWidth-1:0]  wr_data_lo_enc, wr_data_hi_enc;
  logic [FullDataWidth-1:0] wr_data_enc, wr_data_stored;

  assign wr_data_lo = rram_macro_i.wr_data[EccWordWidth-1:0];
  assign wr_data_hi = rram_macro_i.wr_data[DataWidth-1:EccWordWidth];

  prim_secded_hamming_72_64_enc u_ecc_enc_lo (
    .data_i(wr_data_lo),
    .data_o(wr_data_lo_enc)
  );

  prim_secded_hamming_72_64_enc u_ecc_enc_hi (
    .data_i(wr_data_hi),
    .data_o(wr_data_hi_enc)
  );

  assign wr_data_enc    = {wr_data_hi_enc[EccCodeWidth-1:EccWordWidth],
                           wr_data_lo_enc[EccCodeWidth-1:EccWordWidth],
                           wr_data_hi_enc[EccWordWidth-1:0],
                           wr_data_lo_enc[EccWordWidth-1:0]};
  assign wr_data_stored = rram_macro_i.ecc_en ? wr_data_enc : FullDataWidth'(rram_macro_i.wr_data);

  // ECC decode path (read): combinationally decoded from the raw storage word.
  logic [FullDataWidth-1:0] rd_data_raw;
  logic [EccCodeWidth-1:0]  rd_codeword_lo, rd_codeword_hi;
  logic [EccWordWidth-1:0]  rd_data_lo_dec, rd_data_hi_dec;
  logic [1:0]               rd_err_lo, rd_err_hi;
  logic [DataWidth-1:0]     rd_data_dec;
  logic                     rd_data_corr1_err, rd_data_corr2_err, rd_data_fatal_err;

  assign rd_data_raw = mem_rvalid_q ? mem_rdata : mem_rdata_q;

  // Reassemble each 72b codeword from the {ecc1, ecc0, data1, data0} physical layout.
  assign rd_codeword_hi = {rd_data_raw[FullDataWidth-1 -: EccCheckWidth],
                           rd_data_raw[DataWidth-1:EccWordWidth]};
  assign rd_codeword_lo = {rd_data_raw[FullDataWidth-EccCheckWidth-1 -: EccCheckWidth],
                           rd_data_raw[EccWordWidth-1:0]};

  prim_secded_hamming_72_64_dec u_ecc_dec_lo (
    .data_i    (rd_codeword_lo),
    .data_o    (rd_data_lo_dec),
    .syndrome_o(),
    .err_o     (rd_err_lo)
  );

  prim_secded_hamming_72_64_dec u_ecc_dec_hi (
    .data_i    (rd_codeword_hi),
    .data_o    (rd_data_hi_dec),
    .syndrome_o(),
    .err_o     (rd_err_hi)
  );

  assign rd_data_dec = {rd_data_hi_dec, rd_data_lo_dec};

  // ecc_err encoding: single-bit corrected when exactly one half corrects and the other is clean,
  // double-bit corrected when both halves independently correct one bit each, and fatal when
  // either half detects more than one error on its own. See rram_ctrl_pkg::rram_macro_rsp_t.
  assign rd_data_fatal_err = rd_err_lo[1] | rd_err_hi[1];
  assign rd_data_corr2_err = rd_err_lo[0] & rd_err_hi[0];
  assign rd_data_corr1_err = (rd_err_lo[0] ^ rd_err_hi[0]) & ~rd_data_fatal_err;

  logic [11:0] rand_val;
  logic [1:0]  rand_val_read;
  logic [1:0]  rand_val_store;
  logic [7:0]  rand_val_write;
  logic        rand_ack;
  logic        lfsr_en_d, lfsr_en_q;

  assign rram_obs_o = '0;

  // counters
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt_q <= 'h0;
    end else begin
      if (cnt_clr) begin
        cnt_q <= 32'h0;
      end else if (cnt_inc) begin
        cnt_q <= cnt_q + 1'b1;
      end
    end
  end

  // Store partition + write address internally
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      current_part_q <= RramPartData;
      waddr_q        <= '0;
      lfsr_en_q      <= '0;
      ecc_en_q       <= '0;
    end else begin
      current_part_q <= current_part_d;
      waddr_q        <= waddr_d;
      lfsr_en_q      <= lfsr_en_d;
      ecc_en_q       <= ecc_en_d;
    end
  end

  // prim_ram_1p does not guarantee what rdata_o does once req_i goes low again. mem_rvalid_d is
  // asserted by the FSM for the one cycle a read request is issued, so mem_rvalid_q pinpoints the
  // one cycle later mem_rdata is guaranteed valid, and this captures it before it can go stale.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mem_rvalid_q <= 1'b0;
      mem_rdata_q  <= '0;
    end else begin
      mem_rvalid_q <= mem_rvalid_d;
      if (mem_rvalid_q) begin
        mem_rdata_q <= mem_rdata;
      end
    end
  end

  // output assignments
  assign rram_macro_o.done      = done;
  assign rram_macro_o.ack       = ack;
  assign rram_macro_o.rd_data   = rdata;
  assign rram_macro_o.err       = err;
  assign rram_macro_o.ecc_err   = ecc_err;
  assign rram_macro_o.init_done = init_done;

  // LFSR to generate random delays for each operation
  prim_lfsr #(
    .StateOutDw(12),
    .LfsrDw(14)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i('0),
    .seed_i   ('0),
    .lfsr_en_i(lfsr_en_q),
    .entropy_i('0),
    .state_o  (rand_val)
  );

  // 1/8 chance of the ack being 0 in each cycle
  assign rand_ack       = (rand_val[2:0] == '0) ? 1'b0 : 1'b1;
  assign rand_val_read  = rand_val[1:0];
  assign rand_val_store = rand_val[1:0];
  assign rand_val_write = rand_val[7:0];

  always_comb begin
    state_d = state_q;
    fsm_err = 1'b0;

    store_buf_fifo_wvalid = '0;
    store_buf_fifo_wdata  = '0;
    store_buf_fifo_rready = '0;

    mem_req      = '0;
    mem_wr       = '0;
    mem_addr     = '0;
    mem_wdata    = '0;
    mem_rvalid_d = '0;

    err     = 1'b0;
    ecc_err = '0;

    current_part_d = current_part_q;
    waddr_d        = waddr_q;
    ecc_en_d       = ecc_en_q;

    cnt_clr = 1'b0;
    cnt_inc = 1'b0;

    lfsr_en_d = 1'b0;
    init_done = 1'b1;
    done      = 1'b0;
    ack       = 1'b0;
    rdata     = '0;

    unique case (state_q)
      StReset: begin
        init_done = 1'b0;
        state_d   = StInit;
      end

      // Emulate RRAM initialization with a wait timer.
      StInit: begin
        init_done = 1'b0;
        cnt_inc   = 1'b1;
        // Go to idle state if counter >= InitLatency + random_delay
        if (cnt_q >= (InitLatency + rand_val)) begin
          state_d = StIdle;
          cnt_clr = 1'b1;
        end
      end

      // idle state. In this state new requests are accepted.
      StIdle: begin

        // update LFSR value for each request
        if (rram_macro_i.rd_req | rram_macro_i.wr_req) begin
          lfsr_en_d = 1'b1;
        end

        // read request from RRAM
        if (rram_macro_i.rd_req & rand_ack) begin
          ack            = 1'b1;
          current_part_d = rram_macro_i.part;
          ecc_en_d       = rram_macro_i.ecc_en;
          mem_req        = 1'b1;
          mem_addr       = rram_macro_i.addr;
          cnt_inc        = 1'b1;
          state_d        = StRead;
          mem_rvalid_d   = 1'b1;
        // write request to RRAM (wr_last)
        end else if (rram_macro_i.wr_req & rram_macro_i.wr_last & rand_ack) begin
          ack = 1'b1;
          if (!store_buf_fifo_rvalid) begin
            state_d = StRetErr;
          end else begin
            current_part_d = rram_macro_i.part;
            waddr_d        = rram_macro_i.addr;
            cnt_inc        = 1'b1;
            state_d        = StWrite;
          end
        // write request to store buffer
        end else if (rram_macro_i.wr_req & rand_ack) begin
          ack = 1'b1;
          if (store_buf_fifo_full) begin
            state_d = StRetErr;
          end else begin
            store_buf_fifo_wvalid = 1'b1;
            store_buf_fifo_wdata  = {rram_macro_i.addr[WordW-1:0], wr_data_stored};
            state_d = StStoreBuf;
            cnt_inc = 1'b1;
          end
        end
      end

      // Return an error because of an illegal request in the previous cycle
      StRetErr: begin
        state_d = StIdle;
        done    = 1'b1;
        err     = 1'b1;
      end

      // Return data as soon as: counter >= (ReadLatency + random_delay)
      StRead: begin
        cnt_inc = 1'b1;
        // mem_rvalid_q is only true on the cycle mem_rdata is guaranteed valid (see above).
        // Use the registered copy on any other cycle.
        if (cnt_q >= (ReadLatency + rand_val_read)) begin
          done    = 1'b1;
          state_d = StIdle;
          cnt_clr = 1'b1;
          if (ecc_en_q) begin
            rdata   = rd_data_dec;
            ecc_err = {rd_data_fatal_err, rd_data_corr2_err, rd_data_corr1_err};
          end else begin
            rdata = rd_data_raw[DataWidth-1:0];
          end
        end
      end

      // write to internal store buffer and go back to idle state if
      // counter >= (StoreBufLatency + random_delay)
      StStoreBuf: begin
        cnt_inc = 1'b1;
        if (cnt_q >= (StoreBufLatency + rand_val_store)) begin
          state_d = StIdle;
          done    = 1'b1;
          cnt_clr = 1'b1;
        end
      end

      // Read store buffer FIFO and write each word to main array to complete a store operation
      StWrite: begin
        cnt_inc = 1'b1;
        if (store_buf_fifo_rvalid) begin
          store_buf_fifo_rready = 1'b1;
          mem_req   = 1'b1;
          mem_wr    = 1'b1;
          mem_addr  = {waddr_q[DataAddrW-1:WordW], store_buf_fifo_offset};
          mem_wdata = store_buf_fifo_data;
        end else begin
          // return to idle if counter >= WriteLatency + random_delay
          if (cnt_q >= (WriteLatency + rand_val_write)) begin
            done    = 1'b1;
            cnt_clr = 1'b1;
            state_d = StIdle;
          end
        end
      end

      // If the FSM is glitched into an invalid state.
      StErr: begin
        fsm_err = 1'b1;
      end

      default: begin
        state_d = StErr;
        fsm_err = 1'b1;
      end

    endcase // unique case (state_q)
  end // always_comb

  // Store buffer to store page offset + write data. The store buffer can hold up to MaxWrWords
  prim_fifo_sync #(
    .Width(StoreBufWidth),
    .Pass(1'b0),
    .Depth(MaxWrWords)
  ) u_store_buf_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(store_buf_fifo_wvalid),
    .wready_o(),
    .wdata_i (store_buf_fifo_wdata),
    .full_o  (store_buf_fifo_full),
    .depth_o (),
    .rvalid_o(store_buf_fifo_rvalid),
    .rready_i(store_buf_fifo_rready),
    .rdata_o ({store_buf_fifo_offset, store_buf_fifo_data}),
    .err_o   ()
  );


  // Main data array (emulated with prim_ram_1p)
  assign data_mem_req   = (current_part_d == RramPartData) ? mem_req   : '0;
  assign data_mem_wr    = (current_part_d == RramPartData) ? mem_wr    : '0;
  assign data_mem_addr  = (current_part_d == RramPartData) ? mem_addr  : '0;
  assign data_mem_wdata = (current_part_d == RramPartData) ? mem_wdata : '0;

  prim_ram_1p #(
    .Width(FullDataWidth),
    .Depth(TotalDataPages*WordsPerPage),
    .DataBitsPerMask(FullDataWidth)
  ) u_data_array (
    .clk_i,
    .rst_ni,
    .req_i    (data_mem_req),
    .write_i  (data_mem_wr),
    .addr_i   (data_mem_addr),
    .wdata_i  (data_mem_wdata),
    .wmask_i  ({FullDataWidth{1'b1}}),
    .rdata_o  (data_mem_rdata),
    .cfg_i    (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .cfg_o    ()
  );

  // Info array (emulated with prim_ram_1p)
  assign info_mem_req   = (current_part_d == RramPartInfo) ? mem_req                 : '0;
  assign info_mem_wr    = (current_part_d == RramPartInfo) ? mem_wr                  : '0;
  assign info_mem_addr  = (current_part_d == RramPartInfo) ? mem_addr[InfoAddrW-1:0] : '0;
  assign info_mem_wdata = (current_part_d == RramPartInfo) ? mem_wdata               : '0;

  prim_ram_1p #(
    .Width(FullDataWidth),
    .Depth(TotalInfoPages*WordsPerPage),
    .DataBitsPerMask(FullDataWidth)
  ) u_info_array (
    .clk_i,
    .rst_ni,
    .req_i    (info_mem_req),
    .write_i  (info_mem_wr),
    .addr_i   (info_mem_addr),
    .wdata_i  (info_mem_wdata),
    .wmask_i  ({FullDataWidth{1'b1}}),
    .rdata_o  (info_mem_rdata),
    .cfg_i    (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .cfg_o    ()
  );

  // output multiplexer
  assign mem_rdata = (current_part_q == RramPartData) ? data_mem_rdata : info_mem_rdata;

  `ASSERT(EccErrOnehot0_A, $onehot0(rram_macro_o.ecc_err))

  // Alert assertions for reg_we onehot check
  `ASSERT_ERROR_TRIGGER_ERR(MacroFsmCheck_A, u_state_regs, rram_macro_o.fatal_err, 0,
      `_SEC_CM_ALERT_MAX_CYC, unused_err_o, `ASSERT_DEFAULT_CLK, `ASSERT_DEFAULT_RST)
  `ASSUME_FPV(MacroFsmCheck_ATriggerAfterAlertInit_S,
      $stable(rst_ni) == 0 |-> u_state_regs.unused_err_o == 0 [*10])

  `ASSERT_ERROR_TRIGGER_ERR(PrimRegWeOnehotCheck_A,
      u_reg_prim.u_prim_reg_we_check.u_prim_onehot_check, rram_macro_o.fatal_err, 0,
      `_SEC_CM_ALERT_MAX_CYC, err_o, `ASSERT_DEFAULT_CLK, `ASSERT_DEFAULT_RST)
  `ASSUME_FPV(PrimRegWeOneHotCheck_ATriggerAfterAlertInit_S,
      $stable(rst_ni) == 0 |-> u_reg_prim.u_prim_reg_we_check.u_prim_onehot_check.err_o == 0 [*10])

endmodule // rram_macro
