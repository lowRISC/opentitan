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

  typedef enum {P_EDGE = 1, N_EDGE = -1} edge_capture_e;
  edge_capture_e pwr_clk_req_io_ip_clk_edge_capture[$];
  edge_capture_e pwr_ast_req_io_clk_edge_capture[$];
  edge_capture_e pwr_rst_req_rst_lc_req_edge_capture[$];

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
      if (cfg.vif.pwr_ast_req.io_clk_en == 0) cfg.clk_rst_vif.stop_clk();
      if (cfg.vif.pwr_clk_req.io_ip_clk_en == 0) cfg.esc_clk_rst_vif.stop_clk();
      fork
        monitor_pwr_ast_o();
        ctrl_main_clk();
        monitor_pwr_clk_o();
        ctrl_esc_clk();
        monitor_pwr_rst_o();
        ctrl_esc_rst();
      join_none
    end
  endtask

  task monitor_pwr_ast_o();
    logic ival = cfg.vif.pwr_ast_req.io_clk_en;
    forever begin
      if (ival) begin
        // capture negedge
        @(negedge cfg.vif.pwr_ast_req.io_clk_en);
        pwr_ast_req_io_clk_edge_capture.push_back(N_EDGE);
        ival = 0;
      end else begin
        // capture posedge
        @(posedge cfg.vif.pwr_ast_req.io_clk_en);
        pwr_ast_req_io_clk_edge_capture.push_back(P_EDGE);
        ival = 1;
      end // else: !if(ival)
      // handle corner case where reset and clock edge comes very close
      @cfg.vif.cb;
    end
  endtask // monitor_pwr_ast_o

  task monitor_pwr_clk_o();
    logic ival = cfg.vif.pwr_clk_req.io_ip_clk_en;
    forever begin
      if (ival) begin
        // capture negedge
        @(negedge cfg.vif.pwr_clk_req.io_ip_clk_en);
        pwr_clk_req_io_ip_clk_edge_capture.push_back(N_EDGE);
        ival = 0;
      end else begin
        // capture posedge
        @(posedge cfg.vif.pwr_clk_req.io_ip_clk_en);
        pwr_clk_req_io_ip_clk_edge_capture.push_back(P_EDGE);
        ival = 1;
      end
      // move cb to here
      // to address the case where reset and clock edge comes very close
      @cfg.vif.cb;
    end
  endtask // monitor_pwr_clk_o

  task monitor_pwr_rst_o();
    logic ival;
    // Filter out x's in the beginning
    @(cfg.vif.cb);
    ival = cfg.vif.rst_lc_on;
    forever begin
      if (ival) begin
        @(negedge cfg.vif.rst_lc_on);
        pwr_rst_req_rst_lc_req_edge_capture.push_back(N_EDGE);
        ival = 0;
      end else begin
        @(posedge cfg.vif.rst_lc_on);
        pwr_rst_req_rst_lc_req_edge_capture.push_back(P_EDGE);
        ival = 1;
      end
      @cfg.vif.cb;
    end
  endtask // monitor_pwr_rst_o

  task ctrl_main_clk();
    edge_capture_e val;
    forever begin
      @cfg.vif.cb;
      if (pwr_ast_req_io_clk_edge_capture.size() > 0) begin
        val = pwr_ast_req_io_clk_edge_capture.pop_front();
        if (val == P_EDGE) begin
          repeat ($urandom_range(MAIN_CLK_DELAY_MIN, MAIN_CLK_DELAY_MAX)) @cfg.vif.cb;
          cfg.clk_rst_vif.start_clk();
        end else begin
          repeat ($urandom_range(MAIN_CLK_DELAY_MIN, MAIN_CLK_DELAY_MAX)) @cfg.vif.cb;
          cfg.clk_rst_vif.stop_clk();
        end
      end
    end
  endtask // ctrl_main_clk

  task ctrl_esc_clk();
    edge_capture_e val;
    forever begin
      @cfg.vif.cb;
      if (pwr_clk_req_io_ip_clk_edge_capture.size() > 0) begin
        val = pwr_clk_req_io_ip_clk_edge_capture.pop_front();
        if (val == P_EDGE) begin
          repeat ($urandom_range(ESC_CLK_DELAY_MIN, ESC_CLK_DELAY_MAX)) @cfg.vif.cb;
          cfg.esc_clk_rst_vif.start_clk();
        end else begin
          repeat ($urandom_range(ESC_CLK_DELAY_MIN, ESC_CLK_DELAY_MAX)) @cfg.vif.cb;
          cfg.esc_clk_rst_vif.stop_clk();
        end
      end
    end
  endtask // ctrl_esc_clk

  task ctrl_esc_rst();
    edge_capture_e val;
    forever begin
      @cfg.vif.cb;
      if (pwr_rst_req_rst_lc_req_edge_capture.size() > 0) begin
        val = pwr_rst_req_rst_lc_req_edge_capture.pop_front();
        if (val == P_EDGE) begin
          repeat ($urandom_range(ESC_RST_DELAY_MIN, ESC_RST_DELAY_MAX)) @cfg.vif.cb;
          cfg.esc_clk_rst_vif.drive_rst_pin(0);
        end else begin
          repeat ($urandom_range(ESC_RST_DELAY_MIN, ESC_RST_DELAY_MAX)) @cfg.vif.cb;
          cfg.esc_clk_rst_vif.drive_rst_pin(1);
        end
      end
    end // forever begin
  endtask
endclass
