// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface clkmgr_if(input logic clk, input logic rst_n, input logic rst_main_n);
  import clkmgr_env_pkg::*;

  // The ports to the dut side.

  // Encodes the transactional units that are idle.
  logic [NUM_TRANS-1:0] idle_i;

  // pwrmgr req contains ip_clk_en, set to enable the gated clocks.
  pwrmgr_pkg::pwr_clk_req_t pwr_i;

  // outputs clk_status: transitions to 1 if all clocks are enabled, and
  // to 0 when all are disabled.
  pwrmgr_pkg::pwr_clk_rsp_t pwr_o;

  // scanmode_i == lc_ctrl_pkg::On defeats all clock gating.
  lc_ctrl_pkg::lc_tx_t scanmode_i;

  // Life cycle enables clock bypass functionality.
  lc_ctrl_pkg::lc_tx_t lc_dft_en_i;

  // Life cycle clock bypass request and clkmgr ack.
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack;
  // clkmgr clock bypass request and ast ack.
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_ack;

  logic jitter_en_o;
  clkmgr_pkg::clkmgr_ast_out_t clocks_ast_o;
  clkmgr_pkg::clkmgr_out_t clocks_o;

  // Types for CSR values.
  typedef struct packed {
    logic usb_peri_en;
    logic io_peri_en;
    logic io_div2_peri_en;
    logic io_div4_peri_en;
  } clk_enables_t;

  typedef struct packed {
    logic otbn;
    logic kmac;
    logic hmac;
    logic aes;
  } clk_hints_t;

  // The CSR values from the testbench side.
  clk_enables_t        clk_enables;
  clk_hints_t          clk_hints;
  clk_hints_t          clk_hints_status;
  lc_ctrl_pkg::lc_tx_t extclk_sel;
  logic                jitter_enable;

  function automatic void update_extclk_sel(lc_ctrl_pkg::lc_tx_t value);
    extclk_sel = value;
  endfunction

  function automatic void update_clk_enables(clk_enables_t value);
    clk_enables = value;
  endfunction

  function automatic void update_clk_hints(clk_hints_t value);
    clk_hints = value;
  endfunction

  function automatic void update_idle(bit [NUM_TRANS-1:0] value);
    idle_i = value;
  endfunction

  function automatic void update_ip_clk_en(bit value);
    pwr_i.ip_clk_en = value;
  endfunction

  function automatic void update_scanmode(lc_ctrl_pkg::lc_tx_t value);
    scanmode_i = value;
  endfunction

  function automatic logic get_clk_status();
    return pwr_o.clk_status;
  endfunction

  task automatic init(logic [NUM_TRANS-1:0] idle, logic ip_clk_en, lc_ctrl_pkg::lc_tx_t scanmode);
    lc_clk_byp_req = lc_ctrl_pkg::Off;
    ast_clk_byp_ack = lc_ctrl_pkg::Off;
    lc_dft_en_i = lc_ctrl_pkg::Off;
    update_idle(idle);
    update_ip_clk_en(ip_clk_en);
    update_scanmode(scanmode);
  endtask

  // Pipeline signals that go through synchronizers with the target clock domain's clock.
  // thus the PIPELINE_DEPTH is 2.

  // Use clocking blocks clocked by the target clock domain's clock to transfer relevant
  // control signals back to the scoreboard.
  localparam int PIPELINE_DEPTH = 2;

  // Pipelines and clocking blocks for peripheral clocks.

  logic [PIPELINE_DEPTH-1:0] clk_enable_div4_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_div4_ffs;
  always @(posedge clocks_o.clk_io_div4_powerup) begin
    if (rst_n) begin
      clk_enable_div4_ffs <= {clk_enable_div4_ffs[PIPELINE_DEPTH-2:0], clk_enables.io_div4_peri_en};
      ip_clk_en_div4_ffs <= {ip_clk_en_div4_ffs[PIPELINE_DEPTH-2:0], pwr_i.ip_clk_en};
    end
  end
  clocking peri_div4_cb @(posedge clocks_o.clk_io_div4_powerup);
    input ip_clk_en = ip_clk_en_div4_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_div4_ffs[PIPELINE_DEPTH-1];
  endclocking

  logic [PIPELINE_DEPTH-1:0] clk_enable_div2_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_div2_ffs;
  always @(posedge clocks_o.clk_io_div2_powerup) begin
    if (rst_n) begin
      clk_enable_div2_ffs <= {clk_enable_div2_ffs[PIPELINE_DEPTH-2:0], clk_enables.io_div2_peri_en};
      ip_clk_en_div2_ffs <= {ip_clk_en_div2_ffs[PIPELINE_DEPTH-2:0], pwr_i.ip_clk_en};
    end
  end
  clocking peri_div2_cb @(posedge clocks_o.clk_io_div2_powerup);
    input ip_clk_en = ip_clk_en_div2_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_div2_ffs[PIPELINE_DEPTH-1];
  endclocking

  logic [PIPELINE_DEPTH-1:0] clk_enable_io_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_io_ffs;
  always @(posedge clocks_o.clk_io_powerup) begin
    if (rst_n) begin
      clk_enable_io_ffs <= {clk_enable_io_ffs[PIPELINE_DEPTH-2:0], clk_enables.io_peri_en};
      ip_clk_en_io_ffs <= {ip_clk_en_io_ffs[PIPELINE_DEPTH-2:0], pwr_i.ip_clk_en};
    end
  end
  clocking peri_io_cb @(posedge clocks_o.clk_io_powerup);
    input ip_clk_en = ip_clk_en_io_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_io_ffs[PIPELINE_DEPTH-1];
  endclocking

  logic [PIPELINE_DEPTH-1:0] clk_enable_usb_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_usb_ffs;
  always @(posedge clocks_o.clk_usb_powerup) begin
    if (rst_n) begin
      clk_enable_usb_ffs <= {clk_enable_usb_ffs[PIPELINE_DEPTH-2:0], clk_enables.usb_peri_en};
      ip_clk_en_usb_ffs <= {ip_clk_en_usb_ffs[PIPELINE_DEPTH-2:0], pwr_i.ip_clk_en};
    end
  end
  clocking peri_usb_cb @(posedge clocks_o.clk_usb_powerup);
    input ip_clk_en = ip_clk_en_usb_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_usb_ffs[PIPELINE_DEPTH-1];
  endclocking

  // Pipelining and clocking block for transactional unit clocks.

  logic [PIPELINE_DEPTH-1:0][NUM_TRANS-1:0] clk_hints_ffs;
  logic [PIPELINE_DEPTH-1:0]                trans_clk_en_ffs;
  always @(posedge clocks_o.clk_main_powerup) begin
    if (rst_n) begin
      clk_hints_ffs <= {clk_hints_ffs[PIPELINE_DEPTH-2:0], clk_hints};
      trans_clk_en_ffs <= {trans_clk_en_ffs[PIPELINE_DEPTH-2:0], pwr_i.ip_clk_en};
    end
  end
  clocking trans_cb @(posedge clocks_o.clk_main_powerup);
    input ip_clk_en = trans_clk_en_ffs[PIPELINE_DEPTH-1];
    input clk_hints = clk_hints_ffs[PIPELINE_DEPTH-1];
    input idle_i;
  endclocking

endinterface
