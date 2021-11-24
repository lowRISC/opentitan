// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface clkmgr_if (
  input logic clk,
  input logic rst_n,
  input logic rst_io_n,
  input logic rst_main_n,
  input logic rst_usb_n
);
  import clkmgr_env_pkg::*;

  // The ports to the dut side.

  // Encodes the transactional units that are idle.
  logic [NUM_TRANS-1:0] idle_i;

  // pwrmgr req contains ip_clk_en, set to enable the gated clocks.
  pwrmgr_pkg::pwr_clk_req_t pwr_i;

  // outputs clk_status: transitions to 1 if all clocks are enabled, and
  // to 0 when all are disabled.
  pwrmgr_pkg::pwr_clk_rsp_t pwr_o;

  // scanmode_i == MuBi4True defeats all clock gating.
  prim_mubi_pkg::mubi4_t scanmode_i;

  // Life cycle enables clock bypass functionality.
  lc_ctrl_pkg::lc_tx_t lc_dft_en_i;

  // Life cycle clock bypass request and clkmgr ack.
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack;
  // clkmgr clock bypass request and ast ack.
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;

  logic jitter_en_o;
  clkmgr_pkg::clkmgr_out_t clocks_o;

  // Types for CSR values.
  typedef struct packed {
    logic usb_peri_en;
    logic io_peri_en;
    logic io_div2_peri_en;
    logic io_div4_peri_en;
  } clk_enables_t;

  typedef struct packed {
    logic otbn_main;
    logic otbn_io_div4;
    logic kmac;
    logic hmac;
    logic aes;
  } clk_hints_t;

  // The CSR values from the testbench side.
  clk_enables_t          clk_enables_csr;
  clk_hints_t            clk_hints_csr;
  lc_ctrl_pkg::lc_tx_t   extclk_ctrl_csr_sel;
  lc_ctrl_pkg::lc_tx_t   extclk_ctrl_csr_step_down;
  prim_mubi_pkg::mubi4_t jitter_enable_csr;

  // The expected and actual divided io clocks.
  logic                exp_clk_io_div2;
  logic                actual_clk_io_div2;
  logic                exp_clk_io_div4;
  logic                actual_clk_io_div4;

  function automatic void update_extclk_ctrl(logic [2*$bits(lc_ctrl_pkg::lc_tx_t)-1:0] value);
    {extclk_ctrl_csr_step_down, extclk_ctrl_csr_sel} = value;
  endfunction

  function automatic void update_clk_enables(clk_enables_t value);
    clk_enables_csr = value;
  endfunction

  function automatic void update_clk_hints(clk_hints_t value);
    clk_hints_csr = value;
  endfunction

  function automatic void update_idle(bit [NUM_TRANS-1:0] value);
    idle_i = value;
  endfunction

  function automatic void update_io_ip_clk_en(bit value);
    pwr_i.io_ip_clk_en = value;
  endfunction

  function automatic void update_main_ip_clk_en(bit value);
    pwr_i.main_ip_clk_en = value;
  endfunction

  function automatic void update_usb_ip_clk_en(bit value);
    pwr_i.usb_ip_clk_en = value;
  endfunction

  function automatic void update_scanmode(prim_mubi_pkg::mubi4_t value);
    scanmode_i = value;
  endfunction

  function automatic void update_lc_dft_en(lc_ctrl_pkg::lc_tx_t value);
    lc_dft_en_i = value;
  endfunction

  function automatic void update_lc_clk_byp_req(lc_ctrl_pkg::lc_tx_t value);
    lc_clk_byp_req = value;
  endfunction

  function automatic void update_io_clk_byp_ack(prim_mubi_pkg::mubi4_t value);
    io_clk_byp_ack = value;
  endfunction

  // TODO:: this fix is not right since there are now 3 status
  function automatic logic get_clk_status();
    return pwr_o.main_status;
  endfunction

  function automatic void update_jitter_enable(prim_mubi_pkg::mubi4_t value);
    jitter_enable_csr = value;
  endfunction

  function automatic void update_exp_clk_io_divs(logic exp_div2_value, logic actual_div2_value,
                                                 logic exp_div4_value, logic actual_div4_value);
    exp_clk_io_div2 = exp_div2_value;
    actual_clk_io_div2 = actual_div2_value;
    exp_clk_io_div4 = exp_div4_value;
    actual_clk_io_div4 = actual_div4_value;
  endfunction

  task automatic init(logic [NUM_TRANS-1:0] idle, prim_mubi_pkg::mubi4_t scanmode,
                      lc_ctrl_pkg::lc_tx_t lc_dft_en = lc_ctrl_pkg::Off,
                      lc_ctrl_pkg::lc_tx_t lc_clk_byp_req = lc_ctrl_pkg::Off,
                      prim_mubi_pkg::mubi4_t io_clk_byp_ack = prim_mubi_pkg::MuBi4False);
    update_io_clk_byp_ack(io_clk_byp_ack);
    update_idle(idle);
    update_lc_clk_byp_req(lc_clk_byp_req);
    update_lc_dft_en(lc_dft_en);
    update_scanmode(scanmode);
  endtask

  // Pipeline signals that go through synchronizers with the target clock domain's clock.
  // thus the PIPELINE_DEPTH is 2.

  // Use clocking blocks clocked by the target clock domain's clock to transfer relevant
  // control signals back to the scoreboard.
  localparam int PIPELINE_DEPTH = 2;

  // Pipelines and clocking blocks for peripheral clocks.

  logic [PIPELINE_DEPTH-1:0] clk_enable_div4_ffs;
  logic [PIPELINE_DEPTH-1:0] clk_hint_otbn_div4_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_div4_ffs;
  always @(posedge clocks_o.clk_io_div4_powerup or negedge rst_io_n) begin
    if (rst_io_n) begin
      clk_enable_div4_ffs <= {
        clk_enable_div4_ffs[PIPELINE_DEPTH-2:0], clk_enables_csr.io_div4_peri_en
      };
      clk_hint_otbn_div4_ffs <= {
        clk_hint_otbn_div4_ffs[PIPELINE_DEPTH-2:0], clk_hints_csr[TransOtbnIoDiv4]
      };
      ip_clk_en_div4_ffs <= {ip_clk_en_div4_ffs[PIPELINE_DEPTH-2:0], pwr_i.io_ip_clk_en};
    end else begin
      clk_enable_div4_ffs <= '0;
      clk_hint_otbn_div4_ffs <= '0;
      ip_clk_en_div4_ffs <= '0;
    end
  end
  clocking peri_div4_cb @(posedge clocks_o.clk_io_div4_powerup or negedge rst_io_n);
    input ip_clk_en = ip_clk_en_div4_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_div4_ffs[PIPELINE_DEPTH-1];
    input clk_hint_otbn = clk_hint_otbn_div4_ffs[PIPELINE_DEPTH-1];
    input otbn_idle = idle_i[TransOtbnIoDiv4];
  endclocking

  logic [PIPELINE_DEPTH-1:0] clk_enable_div2_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_div2_ffs;
  always @(posedge clocks_o.clk_io_div2_powerup or negedge rst_io_n) begin
    if (rst_io_n) begin
      clk_enable_div2_ffs <= {
        clk_enable_div2_ffs[PIPELINE_DEPTH-2:0], clk_enables_csr.io_div2_peri_en
      };
      ip_clk_en_div2_ffs <= {ip_clk_en_div2_ffs[PIPELINE_DEPTH-2:0], pwr_i.io_ip_clk_en};
    end else begin
      clk_enable_div2_ffs <= '0;
      ip_clk_en_div2_ffs  <= '0;
    end
  end
  clocking peri_div2_cb @(posedge clocks_o.clk_io_div2_powerup or negedge rst_io_n);
    input ip_clk_en = ip_clk_en_div2_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_div2_ffs[PIPELINE_DEPTH-1];
  endclocking

  logic [PIPELINE_DEPTH-1:0] clk_enable_io_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_io_ffs;
  always @(posedge clocks_o.clk_io_powerup or negedge rst_io_n) begin
    if (rst_io_n) begin
      clk_enable_io_ffs <= {clk_enable_io_ffs[PIPELINE_DEPTH-2:0], clk_enables_csr.io_peri_en};
      ip_clk_en_io_ffs  <= {ip_clk_en_io_ffs[PIPELINE_DEPTH-2:0], pwr_i.io_ip_clk_en};
    end else begin
      clk_enable_io_ffs <= '0;
      ip_clk_en_io_ffs  <= '0;
    end
  end
  clocking peri_io_cb @(posedge clocks_o.clk_io_powerup or negedge rst_io_n);
    input ip_clk_en = ip_clk_en_io_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_io_ffs[PIPELINE_DEPTH-1];
  endclocking

  logic [PIPELINE_DEPTH-1:0] clk_enable_usb_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_usb_ffs;
  always @(posedge clocks_o.clk_usb_powerup or negedge rst_usb_n) begin
    if (rst_usb_n) begin
      clk_enable_usb_ffs <= {clk_enable_usb_ffs[PIPELINE_DEPTH-2:0], clk_enables_csr.usb_peri_en};
      ip_clk_en_usb_ffs  <= {ip_clk_en_usb_ffs[PIPELINE_DEPTH-2:0], pwr_i.usb_ip_clk_en};
    end else begin
      clk_enable_usb_ffs <= '0;
      ip_clk_en_usb_ffs  <= '0;
    end
  end
  clocking peri_usb_cb @(posedge clocks_o.clk_usb_powerup or negedge rst_usb_n);
    input ip_clk_en = ip_clk_en_usb_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_usb_ffs[PIPELINE_DEPTH-1];
  endclocking

  // Pipelining and clocking block for transactional unit clocks.
  logic [PIPELINE_DEPTH-1:0][NUM_TRANS-1:0] clk_hints_ffs;
  logic [PIPELINE_DEPTH-1:0]                trans_clk_en_ffs;
  always @(posedge clocks_o.clk_main_powerup or negedge rst_main_n) begin
    if (rst_main_n) begin
      clk_hints_ffs <= {clk_hints_ffs[PIPELINE_DEPTH-2:0], clk_hints_csr};
      trans_clk_en_ffs <= {trans_clk_en_ffs[PIPELINE_DEPTH-2:0], pwr_i.main_ip_clk_en};
    end else begin
      clk_hints_ffs <= '0;
      trans_clk_en_ffs <= '0;
    end
  end
  clocking trans_cb @(posedge clocks_o.clk_main_powerup or negedge rst_main_n);
    input ip_clk_en = trans_clk_en_ffs[PIPELINE_DEPTH-1];
    input clk_hints = clk_hints_ffs[PIPELINE_DEPTH-1];
    input idle_i;
  endclocking

  // Pipelining and clocking block for external clock bypass. The divisor control is
  // triggered by an ast ack, which goes through synchronizers.
  logic step_down_ff;
  always @(posedge clk) begin
    if (rst_n) begin
      step_down_ff <= io_clk_byp_ack == prim_mubi_pkg::MuBi4True;
    end else begin
      step_down_ff <= 1'b0;
    end
  end

  clocking clk_cb @(posedge clk);
    input extclk_ctrl_csr_sel;
    input lc_dft_en_i;
    input io_clk_byp_req;
    input lc_clk_byp_req;
    input step_down = step_down_ff;
    input jitter_enable_csr;
  endclocking

  clocking div_clks_cb @(posedge clocks_o.clk_io_powerup);
    input exp_clk_io_div2;
    input actual_clk_io_div2;
    input exp_clk_io_div4;
    input actual_clk_io_div4;
  endclocking
endinterface
