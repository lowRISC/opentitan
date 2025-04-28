// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from ipgen.clkmgr_gen import get_all_srcs, get_hint_targets, get_rg_srcs
from topgen.lib import Name
rg_srcs = get_rg_srcs(typed_clocks)
hint_targets = get_hint_targets(typed_clocks)
%>\
//
// clkmgr interface.

interface clkmgr_if (
  input logic clk,
  input logic rst_n,
% for src in sorted(src_clks.values(), key=lambda s: s['name']):
<% sep = "" if loop.last else "," %>\
  input logic rst_${src['name']}_n${sep}
% endfor
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
% for clk in [c for c in reversed(typed_clocks['sw_clks'].values())]:
<% sep = "" if loop.last else "," %>\
      ${clk['src_name']}_peri_en: `CLKMGR_HIER.reg2hw.clk_enables.clk_${clk['src_name']}_peri_en.q${sep}
% endfor
    };

  clk_hints_t clk_hints_csr;
  always_comb
    clk_hints_csr = '{
% for target in list(reversed(hint_targets)):
<% sep = '' if loop.last else ',' %>\
    ${target}: `CLKMGR_HIER.reg2hw.clk_hints.clk_main_${target}_hint.q${sep}
% endfor
  };

  clk_hints_t clk_hints_status_csr;
  always_comb
    clk_hints_status_csr = '{
% for target in list(reversed(hint_targets)):
<% sep = '' if loop.last else ',' %>\
                             ${target}: `CLKMGR_HIER.u_reg.clk_hints_status_clk_main_${target}_val_qs${sep}
% endfor
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

% for src in rg_srcs:
  freq_measurement_t ${src}_freq_measurement;
  logic ${src}_timeout_err;
  always @(posedge `CLKMGR_HIER.u_${src}_meas.u_meas.clk_i) begin
    if (`CLKMGR_HIER.u_${src}_meas.u_meas.valid_o) begin
<% spc = " " * (len("      ") + len(src) + len("_freq_measurement = '{")) %>\
      ${src}_freq_measurement = '{valid: `CLKMGR_HIER.u_${src}_meas.u_meas.valid_o,
${spc}slow: `CLKMGR_HIER.u_${src}_meas.u_meas.slow_o,
${spc}fast: `CLKMGR_HIER.u_${src}_meas.u_meas.fast_o};
      `uvm_info("clkmgr_if", $sformatf(
                "Sampled coverage for ClkMesr${Name.to_camel_case(src)} as %p", ${src}_freq_measurement), UVM_HIGH)
    end
  end
  always_comb ${src}_timeout_err = `CLKMGR_HIER.u_${src}_meas.timeout_err_o;

% endfor
  function automatic void update_calib_rdy(prim_mubi_pkg::mubi4_t value);
    calib_rdy = value;
  endfunction

  function automatic void update_idle(mubi_hintables_t value);
    idle_i = value;
  endfunction

% for src in sorted(src_clks.values(), key=lambda s: s['name']):
  % if not src['aon']:
  function automatic void update_${src['name']}_ip_clk_en(bit value);
    pwr_i.${src['name']}_ip_clk_en = value;
  endfunction

  % endif
% endfor
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
% for src in rg_srcs:
      ClkMesr${Name.to_camel_case(src)}: `CLKMGR_HIER.u_${src}_meas.u_meas.cnt = '1;
% endfor
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
    update_all_clk_byp_ack(prim_mubi_pkg::MuBi4False);
  endtask

  // Pipeline signals that go through synchronizers with the target clock domain's clock.
  // thus the PIPELINE_DEPTH is 2.

  // Use clocking blocks clocked by the target clock domain's clock to transfer relevant
  // control signals back to the scoreboard.
  localparam int PIPELINE_DEPTH = 2;

  // Pipelines and clocking blocks for peripheral clocks.

%for clk in typed_clocks['sw_clks'].values():
<%
  clk_name = clk['src_name']
  if clk_name in derived_clks:
    root_name = derived_clks[clk_name]['src']['name']
  else:
    root_name = clk_name
%>\
  logic [PIPELINE_DEPTH-1:0] clk_enable_${clk_name}_ffs;
  logic [PIPELINE_DEPTH-1:0] ip_clk_en_${clk_name}_ffs;
  always @(posedge clocks_o.clk_${clk_name}_powerup or negedge rst_${root_name}_n) begin
    if (rst_${root_name}_n) begin
      clk_enable_${clk_name}_ffs <= {
        clk_enable_${clk_name}_ffs[PIPELINE_DEPTH-2:0], clk_enables_csr.${clk_name}_peri_en
      };
      ip_clk_en_${clk_name}_ffs <= {ip_clk_en_${clk_name}_ffs[PIPELINE_DEPTH-2:0], pwr_i.${root_name}_ip_clk_en};
    end else begin
      clk_enable_${clk_name}_ffs <= '0;
      ip_clk_en_${clk_name}_ffs  <= '0;
    end
  end
  clocking peri_${clk_name}_cb @(posedge clocks_o.clk_${clk_name}_powerup or negedge rst_${root_name}_n);
    input ip_clk_en = ip_clk_en_${clk_name}_ffs[PIPELINE_DEPTH-1];
    input clk_enable = clk_enable_${clk_name}_ffs[PIPELINE_DEPTH-1];
  endclocking

% endfor
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
