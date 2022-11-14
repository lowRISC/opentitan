// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rstmgr_scoreboard extends cip_base_scoreboard #(
  .CFG_T(rstmgr_env_cfg),
  .RAL_T(rstmgr_reg_block),
  .COV_T(rstmgr_env_cov)
);
  `uvm_component_utils(rstmgr_scoreboard)

  // local variables
  static const string sw_rst_ctrl_n_preffix = "sw_rst_ctrl_n_";

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: remove once support alert checking
    do_alert_check = 0;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      monitor_por();
      monitor_capture();
      monitor_tlul_rst();
    join_none
  endtask

  // Start coverage collection after the very first POR negedge, since that transition is not
  // useful for coverage.
  local task monitor_por();
    int stretch_start;
    int reset_count;
    if (!cfg.en_cov) return;
    @(negedge cfg.rstmgr_vif.por_n);
    forever
      @cfg.rstmgr_vif.por_n begin
        if (cfg.rstmgr_vif.por_n == 1'b1) stretch_start = cfg.rstmgr_vif.aon_cycles;
        else begin
          int stretch_cycles = cfg.rstmgr_vif.aon_cycles - stretch_start;
          ++reset_count;
          `DV_CHECK_GT(stretch_cycles, 0)
          cov.reset_stretcher_cg.sample(stretch_cycles, reset_count);
        end
      end
  endtask

  local task monitor_capture();
    if (!cfg.en_cov) return;
    forever
      @cfg.rstmgr_vif.reset_info begin
        if (cfg.rstmgr_vif.reset_info != '0) begin
          cov.alert_info_capture_cg.sample(cfg.rstmgr_vif.reset_info, cfg.rstmgr_vif.alert_info_en);
          cov.cpu_info_capture_cg.sample(cfg.rstmgr_vif.reset_info, cfg.rstmgr_vif.cpu_info_en);
        end
      end
  endtask

  // Monitor tlul reset to update csr_utils_pkg::under_reset variable. This is needed
  // because the tlul reset in rstmgr is generated internally, unlike any other modules
  // where it is controlled by clk_rst_vif.
  local task monitor_tlul_rst();
    forever
      @cfg.m_tl_agent_cfg.vif.rst_n begin
        if (!cfg.m_tl_agent_cfg.vif.rst_n) begin
          `uvm_info(`gfn, "tl got reset", UVM_MEDIUM)
          under_reset = 1;
        end else begin
          `uvm_info(`gfn, "tl got out of reset", UVM_MEDIUM)
          under_reset = 0;
          clear_outstanding_access();
        end
      end
  endtask

  // This converts the trailing digits in a name to a number.
  // It is fatal if there are no trailing digits.
  local function int get_index_from_multibit_name(string name);
    string suffix;
    int last_char_index = name.len() - 1;
    int i;
    for (i = 0; i <= last_char_index; ++i) begin
      byte character = name[last_char_index - i];
      if (character < "0" || character > "9") break;
    end
    `DV_CHECK(i > 0)
    suffix = name.substr(last_char_index - i, last_char_index);
    return suffix.atoi();
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req:
    // for write, update local variable and fifo at address phase,
    // for read, update predication at address phase and compare at data phase.
    // TODO Add support for reading registers with separate write-enable.
    case (csr.get_name())
      // add individual case item for each csr
      "alert_test": begin
        // Write only.
        do_read_check = 1'b0;
      end
      "reset_req": begin
      end
      "reset_info": begin
        // RW1C.
        do_read_check = 1'b0;
      end
      "alert_regwen": begin
        // RW0C.
        // do_read_check = 1'b0;
      end
      "alert_info_ctrl": begin
        // The en bit is cleared by the hardware.
        do_read_check = 1'b0;
      end
      "alert_info_attr": begin
        // Read only.
        do_read_check = 1'b0;
      end
      "alert_info": begin
        // Read only.
        do_read_check = 1'b0;
        if (cfg.en_cov) begin
          cov.alert_info_access_cg.sample(ral.alert_info_ctrl.index.get());
        end
      end
      "cpu_regwen": begin
        // RW0C.
        // do_read_check = 1'b0;
      end
      "cpu_info_ctrl": begin
        // The en bit is cleared by the hardware.
        do_read_check = 1'b0;
      end
      "cpu_info_attr": begin
        // Read only.
        do_read_check = 1'b0;
      end
      "cpu_info": begin
        // Read only.
        do_read_check = 1'b0;
        if (cfg.en_cov) begin
          cov.cpu_info_access_cg.sample(ral.cpu_info_ctrl.index.get());
        end
      end
      "err_code": begin
        // Set by hardware.
        do_read_check = 1'b0;
      end
      default: begin
        if (!uvm_re_match({sw_rst_ctrl_n_preffix, "*"}, csr.get_name())) begin
          `uvm_info(`gfn, $sformatf("write to %0s with 0x%x", csr.get_name(), item.a_data),
                    UVM_MEDIUM)
          do_read_check = 1'b0;
          if (cfg.en_cov && addr_phase_write) begin
            logic enable;
            int i = get_index_from_multibit_name(csr.get_name());
            enable = ral.sw_rst_regwen[i].get();
            cov.sw_rst_cg_wrap[i].sample(enable, item.a_data);
          end
        end else if (!uvm_re_match("sw_rst_regwen_*", csr.get_name())) begin
          // Nothing yet.
        end else begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
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
