// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Phy Write Module
//
// This module implements the RRAM write operations.
// To hide the write latency of the RRAM, data is first written to a store buffer (1-32 words).
// In a second step, the store buffer is written to the actual non volatile array in the RRAM.
// This is similar to:
// https://docs.nordicsemi.com/r/bundle/ps_nrf54L15/page/rramc.html-rram_write_buffered
//
// A write consists of the following operations:
// 1. Incoming data is packed into full RRAM words and the address is injected.
// 2. Data is scrambled (if enabled)
// 3. Data is written to RRAM store buffer (1-32 words, short operations)
// 4. Data is written to RRAM (long operation)
//
// Steps 1-3 are repeated until the "last" indicator has been received, or the address crosses
// a page boundary, in which case a write operation is inserted.
//
// The minimum transfer length of a write operation is one RRAM word (128b).

module rram_phy_wr import rram_ctrl_pkg::*; (
  input  logic                    clk_i,
  input  logic                    rst_ni,
  input  prim_mubi_pkg::mubi4_t   disable_i,
  input  logic                    scramble_en_i,
  input  logic                    ecc_en_i,
  input  logic                    addr_xor_en_i,
  input  logic                    rd_idle_i,
  input  logic                    req_i,
  output logic                    ack_o,
  input  logic [BusAddrW-1:0]     addr_i,
  input  rram_part_e              part_i,
  input  logic [BusFullWidth-1:0] data_i,
  input  logic                    last_i,
  output logic                    done_o,
  output logic                    busy_o,
  // Scrambling module connections
  output scramble_req_t           scramble_req_o,
  input  scramble_rsp_t           scramble_rsp_i,
  // RRAM connections
  output logic                    wr_req_o,
  output logic                    wr_last_o,
  output logic [DataWidth-1:0]    data_o,
  output logic [AddrW-1:0]        addr_o,
  output rram_part_e              part_o,
  output logic                    ecc_en_o,
  input  logic                    ack_i,  // request has been accepted by RRAM
  input  logic                    done_i, // request has been completed
  // Error signals
  output logic                    fsm_err_o,
  output logic                    cnt_err_o,
  output logic                    intg_err_o
);

  logic             word_cnt_en, word_cnt_clr;
  logic [WordW-1:0] word_cnt_q;

  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(WordW),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr)
  ) u_word_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (word_cnt_clr),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (word_cnt_en),
    .decr_en_i         (1'b0),
    .step_i            (WordW'(1'b1)),
    .commit_i          (1'b1),
    .cnt_o             (word_cnt_q),
    .cnt_after_commit_o(),
    .err_o             (cnt_err_o)
  );

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 7 -n 10 \
  //     -s 12343534656 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (47.62%)
  //  6: |||||||||||||||| (38.10%)
  //  7: |||| (9.52%)
  //  8: || (4.76%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StIdle      = 10'b0110100001,
    StCalcMask  = 10'b0011011010,
    StScramble  = 10'b0101111100,
    StStoreBuf  = 10'b1000010000,
    StWrite     = 10'b0001100111,
    StWriteWait = 10'b1111010101,
    StDisabled  = 10'b1100101010
  } state_e;

  state_e state_d, state_q;

  logic [DataWidth-1:0] packed_data_q, packed_data_d;
  logic [WordSelW-1:0]  word_sel;
  logic                 pack_valid;

  logic data_intg_err_q, data_intg_err_d;
  logic busy_d, busy_q;

  logic ecc_en_d, ecc_en_q;

  // use the tlul integrity module directly for bus integrity
  // SEC_CM: MEM.BUS.INTEGRITY
  tlul_data_integ_dec u_data_intg_chk (
    .data_intg_i(data_i),
    .data_err_o (data_intg_err_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_intg_err_q <= '0;
    end else begin
      if (pack_valid) begin
        data_intg_err_q <= data_intg_err_d | data_intg_err_q;
      end
    end
  end

  // Indication to upper layer presence of error
  assign intg_err_o = data_intg_err_q;

  // Scrambling signals
  logic [DataWidth-1:0] mask_q, mask_d;
  logic [AddrW-1:0]     addr_q, addr_d;

  // Current partition
  rram_part_e part_q, part_d;

  // Addr infection signals
  logic [BusWidth-1:0] addr_xor;
  logic [BusWidth-1:0] data_xor;

  logic last_q;

  // SEC_CM: PHY_WR.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StIdle)

  assign word_sel = addr_i[WordSelW-1:0];

  // SEC_CM: MEM.ADDR_INFECTION
  // address infection. It will be removed during read in u_tl_adapter_host or u_rram_ctrl_rd
  assign addr_xor = addr_xor_en_i ? {{(BusWidth-BusAddrW){1'b0}}, addr_i[BusAddrW-1:0]} : '0;
  // in case of data integrity issues, simply fill with 0
  assign data_xor = (data_intg_err_d ? '0 : data_i[BusWidth-1:0]) ^ addr_xor;

  always_comb begin
    state_d = state_q;

    wr_req_o  = 1'b0;
    wr_last_o = 1'b0;

    ack_o     = 1'b0;
    done_o    = 1'b0;
    fsm_err_o = 1'b0;

    word_cnt_en  = 1'b0;
    word_cnt_clr = 1'b0;

    scramble_req_o.calc_req      = 1'b0;
    scramble_req_o.op_req        = 1'b0;
    scramble_req_o.op_type       = ScrambleOp;
    scramble_req_o.addr          = addr_q;
    scramble_req_o.data_in       = '0;
    scramble_req_o.cipher_switch = '0;

    busy_d        = busy_q;
    pack_valid    = 1'b0;
    packed_data_d = packed_data_q;
    ecc_en_d      = ecc_en_q;

    addr_d = addr_q;
    part_d = part_q;
    mask_d = mask_q;

    unique case (state_q)
      StIdle: begin
        if (prim_mubi_pkg::mubi4_test_true_loose(disable_i)) begin
          // Only disable during idle state to ensure write is able to gracefully complete
          state_d = StDisabled;
        end else if (req_i) begin
          ack_o                                        = 1'b1;
          pack_valid                                   = 1'b1;
          packed_data_d[word_sel*BusWidth +: BusWidth] = data_xor;
          part_d                                       = part_i;
          if (word_sel == WidthMultiple - 1) begin
            state_d  = scramble_en_i ? StCalcMask : StStoreBuf;
            addr_d   = addr_i[BusAddrW-1 -: AddrW];
            ecc_en_d = ecc_en_i;
          end else begin
            done_o = 1'b1;
          end
        end
      end

      // Calculate scrambling mask
      StCalcMask: begin
        scramble_req_o.calc_req = 1'b1;
        scramble_req_o.addr     = addr_q;
        if (scramble_rsp_i.calc_ack) begin
          mask_d        = scramble_rsp_i.mask;
          packed_data_d = packed_data_q ^ scramble_rsp_i.mask;
          state_d       = StScramble;
        end
      end

      // Scramble data and remove scrambling mask
      StScramble: begin
        scramble_req_o.op_req  = 1'b1;
        scramble_req_o.data_in = packed_data_q;

        if (scramble_rsp_i.op_ack) begin
          packed_data_d = scramble_rsp_i.data_out ^ mask_q;
          mask_d        = '0;
          state_d       = StStoreBuf;
        end
      end

      // Perform request to store buffer
      StStoreBuf: begin
        if (rd_idle_i) begin
          wr_req_o = 1'b1;
          if (ack_i) begin
            // Clear data from local buffer
            packed_data_d = '0;
            done_o        = 1'b1;
            word_cnt_en   = 1'b1;
            // Write data when
            // - last packet was received
            // - the store buffer is full
            // - the last word of a page is written
            if (last_q || (word_cnt_q == MaxWrWords - 1) || (addr_q[WordW-1:0] == '1)) begin
              busy_d  = 1'b1;
              state_d = StWrite;
            end else begin
              state_d = StIdle;
            end
          end
        end
      end

      // Perform write request to RRAM
      StWrite: begin
        if (rd_idle_i) begin
          wr_req_o  = 1'b1;
          wr_last_o = 1'b1;
          if (ack_i) begin
            state_d = StWriteWait;
          end
        end
      end

      // Wait for write_done
      StWriteWait: begin
        if (done_i) begin
          state_d      = StIdle;
          busy_d       = 1'b0;
          word_cnt_clr = 1'b1;
        end
      end

      StDisabled: begin
        state_d = StDisabled;
      end

      default: begin
        fsm_err_o = 1'b1;
        state_d   = StDisabled;
      end
    endcase // unique case (state_q)
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      packed_data_q <= '0;
      mask_q        <= '0;
      addr_q        <= '0;
      ecc_en_q      <= 1'b1;
      part_q        <= RramPartData;
      busy_q        <= 1'b0;
      last_q        <= 1'b0;
    end else begin
      packed_data_q <= packed_data_d;
      mask_q        <= mask_d;
      addr_q        <= addr_d;
      ecc_en_q      <= ecc_en_d;
      part_q        <= part_d;
      busy_q        <= busy_d;
      if (ack_o) begin
        last_q <= last_i;
      end
    end
  end

  assign busy_o = busy_q;

  assign data_o   = packed_data_q;
  assign addr_o   = addr_q;
  assign part_o   = part_q;
  assign ecc_en_o = ecc_en_q;

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

endmodule // rram_phy_wr
