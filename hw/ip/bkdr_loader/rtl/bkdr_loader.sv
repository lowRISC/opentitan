// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Backdoor loader with indirect programming.

`include "prim_assert.sv"

module bkdr_loader
  import bkdr_loader_pkg::*;
  import bkdr_loader_reg_pkg::*;
(
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Sampled on reset, if set to 1'b1, the bkdr loader is enabled.
  input  logic                        bkdr_ena_i,
  // Upstream JTAG interface connects to the FPGA pad frame
  input  jtag_pkg::jtag_req_t         jtag_req_i,
  output jtag_pkg::jtag_rsp_t         jtag_rsp_o,
  // Downstream JTAG interface connects to Earl Grey's pin mux
  output jtag_pkg::jtag_req_t         jtag_req_o,
  input  jtag_pkg::jtag_rsp_t         jtag_rsp_i,
  // USR_ACCESS register connection
  input  logic[31:0]                  fpga_info_i,
  // Bkdr memory connections
  output bkdr_req_t [NumBkdrTgts-1:0] bkdr_req_o,
  input  bkdr_rsp_t [NumBkdrTgts-1:0] bkdr_rsp_i,
  // Reset towards the downstream system
  output logic                        rst_no
);


  ///////////
  // Types //
  ///////////

  typedef enum logic [1:0] {
    PRELOAD   = 2'h0,
    SWITCHING = 2'h1,
    MISSION   = 2'h2
  } bkdr_state_t;

  typedef enum logic {
    IDLE  = 1'b0,
    CLEAR = 1'b1
  } bkdr_clear_state_t;


  /////////////
  // Signals //
  /////////////

  // State signals
  bkdr_state_t       state_d,       state_q;
  bkdr_clear_state_t clear_state_d, clear_state_q;

  logic bkdr_active;

  // JTAG bus to the internal DTM
  jtag_pkg::jtag_req_t jtag_bkdr_req;
  jtag_pkg::jtag_rsp_t jtag_bkdr_rsp;

  // TL bus between internal DTM and register file
  tlul_pkg::tl_h2d_t regs_tl_h2d;
  tlul_pkg::tl_d2h_t regs_tl_d2h;

  bkdr_loader_reg_pkg::bkdr_loader_regs_reg2hw_t reg2hw;
  bkdr_loader_reg_pkg::bkdr_loader_regs_hw2reg_t hw2reg;

  // Access an invalid target
  logic tgt_idx_err;

  // Was bkdr_ena_i already sampled?
  logic bkdr_ena_sampled_q;

  // Flop the reset output to ensure no glitches on FSM transitions
  logic bkdr_rst_nd, bkdr_rst_nq;

  // Clear FSM signals
  addr_t clear_addr_d, clear_addr_q;
  logic  clear_idle;

  logic [31:0] mission_mode_dly_d, mission_mode_dly_q;

  //////////////
  // Bkdr FSM //
  //////////////

  always_comb begin : proc_bkdr_fsm

    // JTAG tied-off
    jtag_rsp_o    = '0;
    jtag_req_o    = '0;
    jtag_bkdr_req = '0;

    // Keep d/s logic in reset
    bkdr_rst_nd = 1'b0;

    // Keep state
    state_d = state_q;

    // Keep mission mode delay counter
    mission_mode_dly_d = mission_mode_dly_q;

    bkdr_active = 1'b1;

    unique case (state_q)
      PRELOAD : begin
        // Route upstream JTAG port to internal bkdr debug module
        jtag_bkdr_req = jtag_req_i;
        jtag_rsp_o    = jtag_bkdr_rsp;

        // We can only switch from PRELOAD mode to mission mode
        // This either happens in the first cycle after reset when the bkdr_ena_i signal
        // is sampled or on command through the done register.
        if ((reg2hw.control.done.q && reg2hw.control.done.qe && clear_idle) ||
            (!bkdr_ena_sampled_q && !bkdr_ena_i)) begin
          state_d            = SWITCHING;
          mission_mode_dly_d = reg2hw.mission_mode_switch_delay.q;
        end
      end

      SWITCHING : begin
        // Route upstream JTAG port to internal bkdr debug module
        jtag_bkdr_req = jtag_req_i;
        jtag_rsp_o    = jtag_bkdr_rsp;

        if (mission_mode_dly_q == '0) begin
          state_d = MISSION;
        end else begin
          mission_mode_dly_d = mission_mode_dly_q - 'd1;
        end
      end

      MISSION : begin
        // Route upstream JTAG to downstream JTAG
        jtag_req_o  = jtag_req_i;
        jtag_rsp_o  = jtag_rsp_i;
        // Bring downstream system out of reset
        bkdr_rst_nd = 1'b1;
        bkdr_active = 1'b0;
      end

      default:;
    endcase
  end


  ///////////////
  // Clear FSM //
  ///////////////

  always_comb begin : gen_clear_fsm

    clear_idle = 1'b1;

    clear_addr_d  = clear_addr_q;
    clear_state_d = clear_state_q;


    // Don't clear the start bit
    hw2reg.control.clear_start.d  = 1'b0;
    hw2reg.control.clear_start.de = 1'b0;

    unique case (clear_state_q)
      IDLE : begin
        // Clear operation starts
        if (reg2hw.control.clear_start.q && reg2hw.control.clear_start.qe && !tgt_idx_err) begin
          // Clear start bit
          hw2reg.control.clear_start.de = 1'b1;
          clear_state_d = CLEAR;
          clear_addr_d  = '0;
        end
      end

      CLEAR : begin
        clear_idle   = 1'b0;
        clear_addr_d = clear_addr_q + 'd1;
        if (bkdr_rsp_i[reg2hw.control.target_idx.q].param_depth - 'd1 == clear_addr_q) begin
          clear_state_d = IDLE;
        end
      end

      default:;
    endcase
  end

  assign hw2reg.status.clear_idle.d = clear_idle;


  ///////////
  // State //
  ///////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_state
    if(!rst_ni) begin
      state_q <= PRELOAD;
    end else begin
      state_q <= state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_mission_delay
    if(!rst_ni) begin
      mission_mode_dly_q <= '0;
    end else begin
      mission_mode_dly_q <= mission_mode_dly_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_sample_bkdr_ena_sampled
    if(!rst_ni) begin
      bkdr_ena_sampled_q <= 1'b0;
    end else begin
      bkdr_ena_sampled_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_rst_no_flop
    if(!rst_ni) begin
      bkdr_rst_nq <= 1'b0;
    end else begin
      bkdr_rst_nq <= bkdr_rst_nd;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_clear_state
    if(!rst_ni) begin
      clear_state_q <= IDLE;
    end else begin
      clear_state_q <= clear_state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_store_clear_addr
    if(!rst_ni) begin
      clear_addr_q <= '0;
    end else begin
      clear_addr_q <= clear_addr_d;
    end
  end

  assign rst_no = bkdr_rst_nq;


  /////////
  // DTM //
  /////////

  tlul_jtag_dtm #(
    .IdcodeValue(BkdrIdCode),
    .NumDmiByteAbits(bkdr_loader_reg_pkg::RegsAw)
  ) u_tlul_jtag_dtm (
    .clk_i,
    .rst_ni,
    .jtag_i     (jtag_bkdr_req),
    .jtag_o     (jtag_bkdr_rsp),
    .scan_rst_ni(1'b0),
    .scanmode_i (prim_mubi_pkg::MuBi4False),
    .tl_h2d_o   (regs_tl_h2d),
    .tl_d2h_i   (regs_tl_d2h)
  );


  ///////////////////
  // Register file //
  ///////////////////

  bkdr_loader_regs_reg_top u_regs_reg_top (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_h2d),
    .tl_o      (regs_tl_d2h),
    .reg2hw,
    .hw2reg,
    .intg_err_o()
  );

  // Throw error if we address a non-existing target
  assign tgt_idx_err = !(bkdr_idx_e'(reg2hw.control.target_idx.q) inside {BkdrValidTgts});

  assign hw2reg.usr_access_timestamp.d = fpga_info_i;
  assign hw2reg.status.target_error.d  = tgt_idx_err;
  assign hw2reg.read_data              = bkdr_rsp_i[reg2hw.control.target_idx.q].rdata;

  // assign target info registers
  assign hw2reg.num_bkdr_targets = NumBkdrTgts;
  for (genvar i = 0; i < NumBkdrTgts; i++) begin : gen_reg_info_connection
    assign hw2reg.target_info[i].d = BkdrTargets[i];
    assign hw2reg.width_info[i].d  = bkdr_rsp_i[i].param_width;
    assign hw2reg.depth_info[i].d  = bkdr_rsp_i[i].param_depth;
  end

  always_comb begin : proc_format_req
    // Default: forward all data
    for (int unsigned i = 0; i < NumBkdrTgts; i++) begin
      bkdr_req_o[i] = '{
        clk:    clk_i,
        write:  1'b0,
        active: bkdr_active,
        addr:   !clear_idle ? clear_addr_q : reg2hw.index.q,
        wdata:  reg2hw.write_data
      };
    end

    // Strobe endpoint to be written
    bkdr_req_o[reg2hw.control.target_idx.q].write = !clear_idle ||
                                                    (reg2hw.control.write_ena.q &&
                                                     reg2hw.index.qe            &&
                                                     !tgt_idx_err);
  end


  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(RegsTlOutKnown_A,  regs_tl_d2h)

endmodule
