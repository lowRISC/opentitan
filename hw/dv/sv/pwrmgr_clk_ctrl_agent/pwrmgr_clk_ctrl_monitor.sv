// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_clk_ctrl_monitor extends dv_base_monitor #(
    .ITEM_T (pwrmgr_clk_ctrl_item),
    .CFG_T  (pwrmgr_clk_ctrl_agent_cfg),
    .COV_T  (pwrmgr_clk_ctrl_agent_cov)
  );
  `uvm_component_utils(pwrmgr_clk_ctrl_monitor)

  // the base class provides the following handles for use:
  // pwrmgr_clk_ctrl_agent_cfg: cfg
  // pwrmgr_clk_ctrl_agent_cov: cov
  // uvm_analysis_port #(pwrmgr_clk_ctrl_item): analysis_port

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    cfg.vif.wait_for_reset();

    `uvm_info(`gfn, $sformatf("clk_ctrl %s", (cfg.clk_ctrl_en)? "enabled" :
                              "disabled"), UVM_MEDIUM)
    if (cfg.clk_ctrl_en) begin
      fork
        monitor_pwr_ast_o();
        monitor_pwr_clk_o();
      join_none
    end
  endtask

  task monitor_pwr_ast_o();
    forever begin
      @cfg.vif.cb;
      if (cfg.vif.pwr_ast_req.io_clk_en == 0) begin
        cfg.clk_rst_vif.stop_clk();
        @(posedge cfg.vif.pwr_ast_req.io_clk_en);
        repeat ($urandom_range(MAIN_CLK_DELAY_MIN, MAIN_CLK_DELAY_MAX)) @cfg.vif.cb;
        cfg.clk_rst_vif.start_clk();
      end
    end
  endtask // monitor_pwr_ast_o

  task monitor_pwr_clk_o();
    logic ival = cfg.vif.pwr_clk_req.io_ip_clk_en;
    forever begin
      @cfg.vif.cb;
      if (ival) begin
        @(negedge cfg.vif.pwr_clk_req.io_ip_clk_en);
        repeat($urandom_range(ESC_CLK_DELAY_MIN, ESC_CLK_DELAY_MAX)) @cfg.vif.cb;
        cfg.esc_clk_rst_vif.stop_clk();
        ival = 0;
      end else begin
        @(posedge cfg.vif.pwr_clk_req.io_ip_clk_en);
        repeat($urandom_range(ESC_CLK_DELAY_MIN, ESC_CLK_DELAY_MAX)) @cfg.vif.cb;
        cfg.esc_clk_rst_vif.start_clk();
        ival = 1;
      end
    end
  endtask // monitor_pwr_clk_o
endclass
