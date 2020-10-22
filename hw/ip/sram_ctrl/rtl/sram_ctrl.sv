// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SRAM controller.
//

`include "prim_assert.sv"

module sram_ctrl
  import sram_ctrl_reg_pkg::*;
#(
  parameter  int Depth                = 512, // Needs to be a power of 2 if NumAddrScrRounds > 0.
  parameter  int Width                = 32,  // Needs to be Byte aligned for parity
  parameter  int CfgWidth             = 8,   // WTC, RTC, etc
  // Scrambling parameters. Note that this needs to be low-latency, hence we have to keep the
  // amount of cipher rounds low. PRINCE has 5 half rounds in its original form, which corresponds
  // to 2*5 + 1 effective rounds. Setting this to 2 halves this to approximately 5 effective rounds.
  parameter  int NumPrinceRoundsHalf  = 2,   // Number of PRINCE half rounds, can be [1..5]
  // Number of extra intra-Byte diffusion rounds. Setting this to 0 disables intra-Byte diffusion.
  parameter  int NumByteScrRounds     = 2,
  // Number of address scrambling rounds. Setting this to 0 disables address scrambling.
  parameter  int NumAddrScrRounds     = 2,
  // Derived parameters
  localparam int AddrWidth            = prim_util_pkg::vbits(Depth)
) (
  // SRAM Clock
  input                                   clk_i,
  input                                   rst_ni,
  // OTP Clock (for key interface)
  input                                   clk_otp_i,
  input                                   rst_otp_ni,
  // Bus Interface (device) for CSRs
  input  tlul_pkg::tl_h2d_t               tl_i,
  output tlul_pkg::tl_d2h_t               tl_o,
  // Bus Interface (device) for SRAM
  input  tlul_pkg::tl_h2d_t               sram_tl_i,
  output tlul_pkg::tl_d2h_t               sram_tl_o,
  // Interrupt Requests
  output logic                            sram_integ_error_o,
  // Life-cycle escalation input (scraps the scrambling keys)
  input  lc_ctrl_pkg::lc_tx_t             lc_escalate_en_i,
  // Key request to OTP (running on clk_fixed)
  output otp_ctrl_pkg::sram_otp_key_req_t sram_otp_key_o,
  input  otp_ctrl_pkg::sram_otp_key_rsp_t sram_otp_key_i
);

  // This peripheral only works up to a width of 64bits.
  `ASSERT_INIT(WidthMustBeBelow64_A, Width <= 64)

  //////////////////////////
  // CSR Node and Mapping //
  //////////////////////////

  sram_ctrl_reg_pkg::sram_ctrl_reg2hw_t    reg2hw;
  sram_ctrl_reg_pkg::sram_ctrl_hw2reg_t    hw2reg;

  sram_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i (1'b1)
  );

  // Key and attribute outputs to scrambling device
  logic [otp_ctrl_pkg::SramKeyWidth-1:0]   key_d, key_q;
  logic [otp_ctrl_pkg::SramNonceWidth-1:0] nonce_d, nonce_q;
  logic [otp_ctrl_pkg::SramKeyWidth-1:0]   sram_scr_key;
  logic [otp_ctrl_pkg::SramNonceWidth-1:0] sram_scr_nonce;
  logic [CfgWidth-1:0]                     sram_scr_cfg;
  assign sram_scr_key    = key_q;
  assign sram_scr_nonce  = nonce_q;
  assign sram_scr_cfg    = reg2hw.sram_cfg.q;

  // Status register outputs
  logic [AddrWidth-1:0] sram_scr_raddr;
  logic key_valid_d, key_valid_q;
  logic key_seed_valid_d, key_seed_valid_q;
  // Flag an error if any of the error bits is set.
  assign hw2reg.status.error              = |reg2hw.error_type;
  assign hw2reg.status.scr_key_valid      = key_valid_q;
  assign hw2reg.status.scr_key_seed_valid = key_seed_valid_q;

  // Control register
  logic key_req;
  assign key_req = reg2hw.ctrl.q & reg2hw.ctrl.qe;

  // Integrity errors
  logic [1:0] sram_rerror;
  assign hw2reg.error_type.correctable.d    = sram_rerror[0];
  assign hw2reg.error_type.correctable.de   = sram_rerror[0];
  assign hw2reg.error_type.uncorrectable.d  = sram_rerror[1];
  assign hw2reg.error_type.uncorrectable.de = sram_rerror[1];
  assign hw2reg.error_address.d             = 32'(sram_scr_raddr);
  assign hw2reg.error_address.de            = |sram_rerror;

  ////////////////
  // Interrupts //
  ////////////////

  prim_intr_hw #(
    .Width(1)
  ) u_intr_sram_integ_error (
    .clk_i,
    .rst_ni,
    .event_intr_i           ( |sram_rerror         ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.q  ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.de ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.d  ),
    .intr_o                 ( sram_integ_error_o   )
  );

  ///////////////////////////////////
  // Lifecycle Escalation Receiver //
  ///////////////////////////////////

  lc_ctrl_pkg::lc_tx_t escalate_en;
  prim_multibit_sync #(
    .Width(lc_ctrl_pkg::TxWidth),
    .NumChecks (2),
    .ResetValue(lc_ctrl_pkg::TxWidth'(lc_ctrl_pkg::Off))
  ) u_prim_multibit_sync (
    .clk_i,
    .rst_ni,
    .data_i (lc_escalate_en_i),
    .data_o (escalate_en)
  );

  ////////////////////////////
  // Scrambling Key Request //
  ////////////////////////////

  // The scrambling key and nonce have to be requested from the OTP controller via a req/ack
  // protocol. Since the OTP controller works in a different clock domain, we have to synchronize
  // the req/ack protocol as described in more details here:
  // https://docs.opentitan.org/hw/ip/otp_ctrl/doc/index.html#interfaces-to-sram-and-otbn-scramblers
  logic key_ack;
  logic key_req_pending_d, key_req_pending_q;
  assign key_req_pending_d = (key_req) ? 1'b1 :
                             (key_ack) ? 1'b0 : key_req_pending_q;

  assign key_valid_d       = (key_req) ? 1'b0 :
                             (key_ack) ? 1'b1 : key_valid_q;

  assign key_d            = sram_otp_key_i.key;
  assign nonce_d          = sram_otp_key_i.nonce;
  assign key_seed_valid_d = sram_otp_key_i.seed_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      key_req_pending_q <= 1'b0;
      key_valid_q       <= 1'b0;
      key_seed_valid_q  <= 1'b0;
      key_q             <= '0;
      nonce_q           <= '0;
    end else begin
      key_req_pending_q <= key_req_pending_d;
      key_valid_q       <= key_valid_d;
      if (key_ack) begin
        key_seed_valid_q  <= key_seed_valid_d;
        key_q             <= key_d;
        nonce_q           <= nonce_d;
      end
      // This scraps the keys
      if (escalate_en.state != lc_ctrl_pkg::Off) begin
        key_seed_valid_q <= '0;
        key_q            <= '0;
        nonce_q          <= '0;
      end
    end
  end

  prim_sync_reqack u_prim_sync_reqack (
    .clk_src_i  ( clk_i              ),
    .rst_src_ni ( rst_ni             ),
    .clk_dst_i  ( clk_otp_i          ),
    .rst_dst_ni ( rst_otp_ni         ),
    .src_req_i  ( key_req_pending_q  ),
    .src_ack_o  ( key_ack            ),
    .dst_req_o  ( sram_otp_key_o.req ),
    .dst_ack_i  ( sram_otp_key_i.ack )
  );

  ////////////////////////////////
  // Scrambled Memory Primitive //
  ////////////////////////////////

  logic tlul_req;
  logic tlul_we;
  logic [AddrWidth-1:0] tlul_addr;
  logic [Width-1:0] tlul_wdata;
  logic [Width-1:0] tlul_wmask;
  logic [Width-1:0] tlul_rdata;
  logic tlul_rvalid;
  logic [1:0] tlul_rerror;

  tlul_adapter_sram #(
    .SramAw(AddrWidth),
    .SramDw(Width)
  ) u_tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .tl_i     ( sram_tl_i   ),
    .tl_o     ( sram_tl_o   ),
    .req_o    ( tlul_req    ),
    .gnt_i    ( 1'b1        ),
    .we_o     ( tlul_we     ),
    .addr_o   ( tlul_addr   ),
    .wdata_o  ( tlul_wdata  ),
    .wmask_o  ( tlul_wmask  ),
    .rdata_i  ( tlul_rdata  ),
    .rvalid_i ( tlul_rvalid ),
    .rerror_i ( tlul_rerror )
  );

  logic sram_req;
  logic sram_we;
  logic [AddrWidth-1:0] sram_addr;
  logic [Width-1:0] sram_wdata;
  logic [Width-1:0] sram_wmask;
  logic [Width-1:0] sram_rdata;
  logic sram_rvalid;

  prim_ram_1p_scr #(
    .Depth               ( Depth               ),
    .Width               ( Width               ),
    .CfgWidth            ( CfgWidth            ),
    .NumPrinceRoundsHalf ( NumPrinceRoundsHalf ),
    .NumByteScrRounds    ( NumByteScrRounds    ),
    .NumAddrScrRounds    ( NumAddrScrRounds    )
  ) i_prim_ram_1p_scr (
    .clk_i,
    .rst_ni,
    .key_i    ( sram_scr_key   ),
    .nonce_i  ( sram_scr_nonce ),
    .req_i    ( sram_req       ),
    .write_i  ( sram_we        ),
    .addr_i   ( sram_addr      ),
    .wdata_i  ( sram_wdata     ),
    .wmask_i  ( sram_wmask     ),
    .rdata_o  ( sram_rdata     ),
    .rvalid_o ( sram_rvalid    ),
    .rerror_o ( sram_rerror    ),
    .raddr_o  ( sram_scr_raddr ),
    .cfg_i    ( sram_scr_cfg   )
  );

  // Do not forward requests to SRAM while key request is pending.
  // Instead, we return a TLUL error.
  assign sram_req    = ~key_req_pending_q & tlul_req;
  assign sram_we     = ~key_req_pending_q & tlul_we;
  assign sram_addr   = tlul_addr;
  assign sram_wdata  = tlul_wdata;
  assign sram_wmask  = tlul_wmask;

  // Delay the key pending error by one cycle in order to match with the SRAM read latency.
  logic  key_pending_error_d, key_pending_error_q;
  assign key_pending_error_d = key_req_pending_q & tlul_req;
  assign tlul_rdata  = (key_pending_error_q) ? '0    : sram_rdata;
  assign tlul_rvalid = (key_pending_error_q) ? 1'b1  : sram_rvalid;
  assign tlul_rerror = (key_pending_error_q) ? 2'b10 : sram_rerror; // signal as uncorrectable

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_error_reg
    if (!rst_ni) begin
      key_pending_error_q <= 1'b0;
    end else begin
      key_pending_error_q <= key_pending_error_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlOutKnown_A,                tl_o)
  `ASSERT_KNOWN(TlSramOutKnown_A,            sram_tl_o)
  `ASSERT_KNOWN(IntrSramParityErrorKnown_A,  sram_integ_error_o)
  `ASSERT_KNOWN(SramOtpKeyKnown_A,           sram_otp_key_o)

endmodule : sram_ctrl
