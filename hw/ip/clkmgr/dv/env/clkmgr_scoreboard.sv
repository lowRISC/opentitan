// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The scoreboard checks ast_clk_byp_req is driven in response to an external clock request,
// drives ast_clk_byp_ack response, checks the jitter_an_o output, and processes CSR checks.
class clkmgr_scoreboard extends cip_base_scoreboard #(
  .CFG_T(clkmgr_env_cfg),
  .RAL_T(clkmgr_reg_block),
  .COV_T(clkmgr_env_cov)
);
  `uvm_component_utils(clkmgr_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      monitor_ast_clk_byp();
      monitor_jitter_en();
    join_none
  endtask

  task monitor_ast_clk_byp();
    lc_tx_t prev_lc_clk_byp_req = Off;
    forever
      @cfg.clkmgr_vif.clk_cb begin
        if (cfg.clkmgr_vif.lc_clk_byp_req != prev_lc_clk_byp_req) begin
          `uvm_info(`gfn, $sformatf(
                    "Got lc_clk_byp_req %s", cfg.clkmgr_vif.lc_clk_byp_req == On ? "On" : "Off"),
                    UVM_MEDIUM)
          prev_lc_clk_byp_req = cfg.clkmgr_vif.lc_clk_byp_req;
        end
        if (cfg.clk_rst_vif.rst_n) begin
          if (((cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_sel == On) &&
               (cfg.clkmgr_vif.clk_cb.lc_dft_en_i == On)) ||
              (cfg.clkmgr_vif.clk_cb.lc_clk_byp_req == On)) begin
            `DV_CHECK_EQ(cfg.clkmgr_vif.ast_clk_byp_req, On, "Expected ast_clk_byp_req to be On")
          end
          if (cfg.en_cov) begin
            cov.extclk_cg.sample(cfg.clkmgr_vif.clk_cb.extclk_ctrl_csr_sel,
                                 cfg.clkmgr_vif.clk_cb.lc_dft_en_i,
                                 cfg.clkmgr_vif.clk_cb.lc_clk_byp_req, cfg.clkmgr_vif.scanmode_i);
          end
        end
      end
  endtask

  task monitor_jitter_en();
    fork
      forever
        @cfg.clkmgr_vif.clk_cb begin
          if (cfg.clk_rst_vif.rst_n) begin
            @cfg.clkmgr_vif.jitter_enable_csr begin
              cfg.clk_rst_vif.wait_clks(2);
              `DV_CHECK_EQ(cfg.clkmgr_vif.jitter_en_o, cfg.clkmgr_vif.jitter_enable_csr,
                           "Mismatching jitter enable output")
            end
          end
        end
      forever
        @cfg.clkmgr_vif.clk_cb begin
          if (cfg.clk_rst_vif.rst_n) begin
            @cfg.clkmgr_vif.jitter_en_o begin
              cfg.clk_rst_vif.wait_clks(2);
              `DV_CHECK_EQ(cfg.clkmgr_vif.jitter_en_o, cfg.clkmgr_vif.jitter_enable_csr,
                           "Mismatching jitter enable output")
            end
          end
        end
    join
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    string         access_str = write ? "write" : "read";
    string         channel_str = channel == AddrChannel ? "address" : "data";

    logic          extclk_ctrl_regwen = ral.extclk_ctrl_regwen.get_reset();

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // If incoming access is a write to a valid csr, update prediction right away.
    if (addr_phase_write) begin
      `uvm_info(`gfn, $sformatf("Writing 0x%0x to %s", item.a_data, csr.get_name()), UVM_MEDIUM)
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // Process the csr req:
    // - For write, update local variable and fifo at address phase.
    // - For read, update predication at address phase and compare at data phase.
    case (csr.get_name())
      // add individual case item for each csr
      "alert_test": begin
        // FIXME
      end
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "extclk_ctrl_regwen": begin
        if (addr_phase_write) begin
          extclk_ctrl_regwen = item.a_data;
        end
      end
      "extclk_ctrl": begin
        if (addr_phase_write && extclk_ctrl_regwen) begin
          cfg.clkmgr_vif.update_extclk_ctrl(item.a_data);
        end
      end
      "jitter_enable": begin
        if (addr_phase_write) begin
          cfg.clkmgr_vif.update_jitter_enable(item.a_data);
        end
      end
      "clk_enables": begin
        if (addr_phase_write) begin
          cfg.clkmgr_vif.update_clk_enables(item.a_data);
        end
      end
      "clk_hints": begin
        // Clearing a hint sets an expectation for the status to transition to zero.
        if (addr_phase_write) begin
          cfg.clkmgr_vif.update_clk_hints(item.a_data);
        end
      end
      "clk_hints_status": begin
        // The status will respond to the hint once the target unit is idle. We check it in
        // the sequence.
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      `uvm_info(`gfn, $sformatf("Reading 0x%0x from %s", item.d_data, csr.get_name()), UVM_MEDIUM)
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
