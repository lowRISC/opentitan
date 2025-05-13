// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(soc_dbg_ctrl_env_cfg),
    .RAL_T(soc_dbg_ctrl_core_reg_block),
    .COV_T(soc_dbg_ctrl_env_cov)
  );
  `uvm_component_utils(soc_dbg_ctrl_scoreboard)

  // Local variables

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Class specific methods
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern task process_tl_core_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
    tl_phase_e tl_phase);
  extern task process_tl_jtag_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
    tl_phase_e tl_phase);
  extern function void reset(string kind = "HARD");
endclass : soc_dbg_ctrl_scoreboard


function soc_dbg_ctrl_scoreboard::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void soc_dbg_ctrl_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // TODO: remove once support alert checking
  do_alert_check = 0;
endfunction : build_phase

function void soc_dbg_ctrl_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

task soc_dbg_ctrl_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  wait(cfg.under_reset);
  forever begin
    wait(!cfg.under_reset);
    // This isolation fork is needed to ensure that "disable fork" call won't kill any other
    // processes at the same level from the parent classes
    fork begin : isolation_fork
      fork
        begin : main_thread
          fork
            // TODO remove this entire forever loop and replace it with something more meaningful
            // it's just a placeholder to avoid simulation hanging
            forever begin
              cfg.clk_rst_vif.wait_clks(1);
            end
          join
          wait fork;  // To ensure it will be killed only when the reset will occur
        end
        begin : reset_thread
          wait(cfg.under_reset);
        end
      join_any
      disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
    end join
  end
endtask : run_phase

task soc_dbg_ctrl_scoreboard::process_tl_access(tl_seq_item item,
                                                tl_channels_e channel,
                                                string ral_name);
  bit            write    = item.is_write();
  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
  tl_phase_e     tl_phase;

  if (!write && channel == AddrChannel) tl_phase = AddrRead;
  if ( write && channel == AddrChannel) tl_phase = AddrWrite;
  if (!write && channel == DataChannel) tl_phase = DataRead;
  if ( write && channel == DataChannel) tl_phase = DataWrite;

  if (ral_name == ral.get_name()) begin
    process_tl_core_access(item, csr_addr, tl_phase);
  end else if (ral_name == cfg.jtag_ral_name) begin
    process_tl_jtag_access(item, csr_addr, tl_phase);
  end else begin
    `uvm_fatal(`gfn, $sformatf("Specified RAL name %0s doesn't exist!", ral_name))
  end
endtask : process_tl_access

task soc_dbg_ctrl_scoreboard::process_tl_core_access(
  tl_seq_item item, uvm_reg_addr_t csr_addr, tl_phase_e tl_phase);
  string  ral_name      = ral.get_name();
  bit     do_read_check = 1;
  uvm_reg csr;

  // If access was to a valid CSR, get the CSR handle
  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
  end else begin
    `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
  end

  // If incoming access is a write to a valid csr, then make updates right away
  if (tl_phase == AddrWrite) begin
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
  end

  // Process the CRS req:
  //  - for write, update local variable and fifo at address phase
  //  - for read, update predication at address phase and compare at data phase
  case (csr.get_name())
    // Add individual case item for each csr
    "intr_state": begin
      // FIXME TODO MVy
      do_read_check = 1'b0;
    end
    "intr_enable": begin
      // FIXME TODO MVy
    end
    "intr_test": begin
      // FIXME TODO MVy
    end
    "debug_policy_relocked": begin
      // FIXME TODO
    end
    default: begin
      `uvm_fatal(`gfn, $sformatf("invalid CSR: %0s", csr.get_full_name()))
    end
  endcase

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (tl_phase == DataRead) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask : process_tl_core_access

task soc_dbg_ctrl_scoreboard::process_tl_jtag_access(
  tl_seq_item item, uvm_reg_addr_t csr_addr, tl_phase_e tl_phase);
  string  ral_name      = cfg.jtag_ral_name;
  bit     do_read_check = 1;
  uvm_reg csr;
  // TODO
  `uvm_info(`gfn, "Tmp debug: tl_jtag_access detected", UVM_LOW)
endtask : process_tl_jtag_access

function void soc_dbg_ctrl_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  // Reset local fifos queues and variables
endfunction : reset

function void soc_dbg_ctrl_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  // Post test checks - ensure that all local fifos and queues are empty
endfunction : check_phase
