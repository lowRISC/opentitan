// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface.

interface clkmgr_if (
  input logic clk,
  input logic rst_n,
  input logic clk_main,
  input logic rst_io_n,
  input logic rst_main_n,
  input logic rst_usb_n
);
  import uvm_pkg::*;
  import clkmgr_env_pkg::*;

  // The ports to the dut side.

  localparam int LcTxTWidth = $bits(lc_ctrl_pkg::lc_tx_t);

  // Encodes the transactional units that are idle.
  mubi_hintables_t idle_i;

  // pwrmgr req contains ip_clk_en, set to enable the gated clocks.
  pwrmgr_pkg::pwr_clk_req_t pwr_i;

  // outputs clk_status: transitions to 1 if all clocks are enabled, and
  // to 0 when all are disabled.
  pwrmgr_pkg::pwr_clk_rsp_t pwr_o;

  // scanmode_i == MuBi4True defeats all clock gating.
  prim_mubi_pkg::mubi4_t scanmode_i;

  // Life cycle enables clock bypass functionality.
  lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i;

  // Life cycle clock bypass request and clkmgr ack.
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack;
  // clkmgr clock bypass request for io clocks and ast ack: triggered by lc_clk_byp_req.
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  // clkmgr clock bypass request for all clocks and ast ack: triggered by software.
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;

  prim_mubi_pkg::mubi4_t div_step_down_req;

  prim_mubi_pkg::mubi4_t jitter_en_o;
  clkmgr_pkg::clkmgr_out_t clocks_o;

  prim_mubi_pkg::mubi4_t calib_rdy;
  prim_mubi_pkg::mubi4_t hi_speed_sel;

  // Internal DUT signals.
  // ICEBOX(lowrisc/opentitan#18379): This is a core env component (i.e. reusable entity) that
  // makes hierarchical references into the DUT. A better strategy would be to bind this interface
  // to the DUT in tb.sv and use relative paths instead.
`ifndef CLKMGR_HIER
  `define CLKMGR_HIER tb.dut
`endif

  // The CSR values from the testbench side.
  clk_enables_t clk_enables_csr;
  always_comb
    clk_enables_csr = '{
    usb_peri_en: `CLKMGR_HIER.reg2hw.clk_enables.clk_usb_peri_en.q,
    io_peri_en: `CLKMGR_HIER.reg2hw.clk_enables.clk_io_peri_en.q,
    io_div2_peri_en: `CLKMGR_HIER.reg2hw.clk_enables.clk_io_div2_peri_en.q,
    io_div4_peri_en: `CLKMGR_HIER.reg2hw.clk_enables.clk_io_div4_peri_en.q
  };

  clk_hints_t clk_hints_csr;
  always_comb
    clk_hints_csr = '{
    otbn_main: `CLKMGR_HIER.reg2hw.clk_hints.clk_main_otbn_hint.q,
    kmac: `CLKMGR_HIER.reg2hw.clk_hints.clk_main_kmac_hint.q,
    hmac: `CLKMGR_HIER.reg2hw.clk_hints.clk_main_hmac_hint.q,
    aes: `CLKMGR_HIER.reg2hw.clk_hints.clk_main_aes_hint.q
  };

  clk_hints_t clk_hints_status_csr;
  always_comb
    clk_hints_status_csr = '{
                             otbn_main: `CLKMGR_HIER.u_reg.clk_hints_status_clk_main_otbn_val_qs,
                             kmac: `CLKMGR_HIER.u_reg.clk_hints_status_clk_main_kmac_val_qs,
                             hmac: `CLKMGR_HIER.u_reg.clk_hints_status_clk_main_hmac_val_qs,
                             aes: `CLKMGR_HIER.u_reg.clk_hints_status_clk_main_aes_val_qs
                             };

  prim_mubi_pkg::mubi4_t extclk_ctrl_csr_sel;
  always_comb begin
    extclk_ctrl_csr_sel = prim_mubi_pkg::mubi4_t'(`CLKMGR_HIER.reg2hw.extclk_ctrl.sel.q);
  end

  prim_mubi_pkg::mubi4_t extclk_ctrl_csr_step_down;
  always_comb begin
    extclk_ctrl_csr_step_down = prim_mubi_pkg::mubi4_t'(
        `CLKMGR_HIER.reg2hw.extclk_ctrl.hi_speed_sel.q);
  end

  prim_mubi_pkg::mubi4_t jitter_enable_csr;
  always_comb begin
    jitter_enable_csr = prim_mubi_pkg::mubi4_t'(`CLKMGR_HIER.reg2hw.jitter_enable.q);
  end

  freq_measurement_t io_freq_measurement;
  logic io_timeout_err;
  always @(posedge `CLKMGR_HIER.u_io_meas.u_meas.clk_i) begin
    if (`CLKMGR_HIER.u_io_meas.u_meas.valid_o) begin
      io_freq_measurement = '{valid: `CLKMGR_HIER.u_io_meas.u_meas.valid_o,
                              slow: `CLKMGR_HIER.u_io_meas.u_meas.slow_o,
                              fast: `CLKMGR_HIER.u_io_meas.u_meas.fast_o};
      `uvm_info("clkmgr_if", $sformatf("Sampled coverage for ClkMesrIo as %p", io_freq_measurement),
                UVM_HIGH)
    end
  end
  always_comb io_timeout_err = `CLKMGR_HIER.u_io_meas.timeout_err_o;

  freq_measurement_t io_div2_freq_measurement;
  logic io_div2_timeout_err;
  always @(posedge `CLKMGR_HIER.u_io_div2_meas.u_meas.clk_i) begin
    if (`CLKMGR_HIER.u_io_div2_meas.u_meas.valid_o) begin
      io_div2_freq_measurement = '{valid: `CLKMGR_HIER.u_io_div2_meas.u_meas.valid_o,
                                   slow: `CLKMGR_HIER.u_io_div2_meas.u_meas.slow_o,
                                   fast: `CLKMGR_HIER.u_io_div2_meas.u_meas.fast_o};
      `uvm_info("clkmgr_if", $sformatf(
                "Sampled coverage for ClkMesrIoDiv2 as %p", io_div2_freq_measurement), UVM_HIGH)
    end
  end
  always_comb io_div2_timeout_err = `CLKMGR_HIER.u_io_div2_meas.timeout_err_o;

  freq_measurement_t io_div4_freq_measurement;
  logic io_div4_timeout_err;
  always @(posedge `CLKMGR_HIER.u_io_div4_meas.u_meas.clk_i) begin
    if (`CLKMGR_HIER.u_io_div4_meas.u_meas.valid_o) begin
      io_div4_freq_measurement = '{valid: `CLKMGR_HIER.u_io_div4_meas.u_meas.valid_o,
                                   slow: `CLKMGR_HIER.u_io_div4_meas.u_meas.slow_o,
                                   fast: `CLKMGR_HIER.u_io_div4_meas.u_meas.fast_o};
      `uvm_info("clkmgr_if", $sformatf(
                "Sampled coverage for ClkMesrIoDiv4 as %p", io_div4_freq_measurement), UVM_HIGH)
    end
  end
  always_comb io_div4_timeout_err = `CLKMGR_HIER.u_io_div4_meas.timeout_err_o;

  freq_measurement_t main_freq_measurement;
  logic main_timeout_err;
  always @(posedge `CLKMGR_HIER.u_main_meas.u_meas.clk_i) begin
    if (`CLKMGR_HIER.u_main_meas.u_meas.valid_o) begin
      main_freq_measurement = '{valid: `CLKMGR_HIER.u_main_meas.u_meas.valid_o,
                                slow: `CLKMGR_HIER.u_main_meas.u_meas.slow_o,
                                fast: `CLKMGR_HIER.u_main_meas.u_meas.fast_o};
      `uvm_info("clkmgr_if", $sformatf(
                "Sampled coverage for ClkMesrMain as %p", main_freq_measurement), UVM_HIGH)
    end
  end
  always_comb main_timeout_err = `CLKMGR_HIER.u_main_meas.timeout_err_o;

  freq_measurement_t usb_freq_measurement;
  logic usb_timeout_err;
  always @(posedge `CLKMGR_HIER.u_usb_meas.u_meas.clk_i) begin
    if (`CLKMGR_HIER.u_usb_meas.u_meas.valid_o) begin
      usb_freq_measurement = '{valid: `CLKMGR_HIER.u_usb_meas.u_meas.valid_o,
                               slow: `CLKMGR_HIER.u_usb_meas.u_meas.slow_o,
                               fast: `CLKMGR_HIER.u_usb_meas.u_meas.fast_o};
      `uvm_info("clkmgr_if", $sformatf("Sampled coverage for ClkMesrUsb as %p", usb_freq_measurement
                ), UVM_HIGH)
    end
  end
  always_comb usb_timeout_err = `CLKMGR_HIER.u_usb_meas.timeout_err_o;

  function automatic void update_calib_rdy(prim_mubi_pkg::mubi4_t value);
    calib_rdy = value;
  endfunction

  function automatic void update_idle(mubi_hintables_t value);
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

  function automatic void update_lc_debug_en(lc_ctrl_pkg::lc_tx_t value);
    lc_hw_debug_en_i = value;
  endfunction

  function automatic void update_lc_clk_byp_req(lc_ctrl_pkg::lc_tx_t value);
    lc_clk_byp_req = value;
  endfunction

  function automatic void update_all_clk_byp_ack(prim_mubi_pkg::mubi4_t value);
    `uvm_info("clkmgr_if", $sformatf("In clkmgr_if update_all_clk_byp_ack with %b", value),
              UVM_MEDIUM)
    all_clk_byp_ack = value;
  endfunction

  function automatic void update_div_step_down_req(prim_mubi_pkg::mubi4_t value);
    `uvm_info("clkmgr_if", $sformatf("In clkmgr_if update_div_step_down_req with %b", value),
              UVM_MEDIUM)
    div_step_down_req = value;
  endfunction

  function automatic void update_io_clk_byp_ack(prim_mubi_pkg::mubi4_t value);
    io_clk_byp_ack = value;
  endfunction

  function automatic void force_high_starting_count(clk_mesr_e clk);
    `uvm_info("clkmgr_if", $sformatf("Forcing count of %0s to all 1.", clk.name()), UVM_MEDIUM)
    case (clk)
      ClkMesrIo: `CLKMGR_HIER.u_io_meas.u_meas.cnt = '1;
      ClkMesrIoDiv2: `CLKMGR_HIER.u_io_div2_meas.u_meas.cnt = '1;
      ClkMesrIoDiv4: `CLKMGR_HIER.u_io_div4_meas.u_meas.cnt = '1;
      ClkMesrMain: `CLKMGR_HIER.u_main_meas.u_meas.cnt = '1;
      ClkMesrUsb: `CLKMGR_HIER.u_usb_meas.u_meas.cnt = '1;
      default: ;
    endcase
  endfunction

  task automatic init(mubi_hintables_t idle, prim_mubi_pkg::mubi4_t scanmode,
                      lc_ctrl_pkg::lc_tx_t lc_debug_en = lc_ctrl_pkg::Off,
                      lc_ctrl_pkg::lc_tx_t lc_clk_byp_req = lc_ctrl_pkg::Off,
                      prim_mubi_pkg::mubi4_t calib_rdy = prim_mubi_pkg::MuBi4True);
    `uvm_info("clkmgr_if", "In clkmgr_if init", UVM_MEDIUM)
    update_calib_rdy(calib_rdy);
    update_idle(idle);
    update_lc_clk_byp_req(lc_clk_byp_req);
    update_lc_debug_en(lc_debug_en);
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
  always @(posedge clocks_o.clk_io_div4_powerup or negedge rst_io_n) begin
    if (rst_io_n) begin
      clk_enable_div4_ffs <= {
        clk_enable_div4_ffs[PIPELINE_DEPTH-2:0], clk_enables_csr.io_div4_peri_en
      };
      ip_clk_en_div4_ffs <= {ip_clk_en_div4_ffs[PIPELINE_DEPTH-2:0], pwr_i.io_ip_clk_en};
    end else begin
      clk_enable_div4_ffs <= '0;
      ip_clk_en_div4_ffs  <= '0;
    end
  end
  clocking peri_div4_cb @(posedge clocks_o.clk_io_div4_powerup or negedge rst_io_n);
    input ip_clk_en = ip_clk_en_div4_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_div4_ffs[PIPELINE_DEPTH-1];
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
    input calib_rdy;
    input extclk_ctrl_csr_sel;
    input extclk_ctrl_csr_step_down;
    input lc_hw_debug_en_i;
    input io_clk_byp_req;
    input lc_clk_byp_req;
    input step_down = step_down_ff;
    input jitter_enable_csr;
  endclocking

endinterface
