// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_scoreboard extends cip_base_scoreboard #(
    .CFG_T(ac_range_check_env_cfg),
    .RAL_T(ac_range_check_reg_block),
    .COV_T(ac_range_check_env_cov)
  );
  `uvm_component_utils(ac_range_check_scoreboard)

  // Local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_fifo;

  // Local queues to hold incoming packets pending comparison
  tl_seq_item tl_unfilt_q[$];
  tl_seq_item tl_filt_q[$];

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Class specific methods
  extern task process_tl_unfilt_fifo();
  extern task process_tl_filt_fifo();
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern function void reset(string kind = "HARD");
endclass : ac_range_check_scoreboard


function ac_range_check_scoreboard::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void ac_range_check_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  tl_unfilt_fifo = new("tl_unfilt_fifo", this);
  tl_filt_fifo   = new("tl_filt_fifo", this);
  // TODO: remove once support alert checking
  do_alert_check = 0;
endfunction : build_phase

function void ac_range_check_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase

task ac_range_check_scoreboard::run_phase(uvm_phase phase);
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
            process_tl_unfilt_fifo();
            process_tl_filt_fifo();
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

task ac_range_check_scoreboard::process_tl_unfilt_fifo();
  tl_seq_item item;
  forever begin
    tl_unfilt_fifo.get(item);
    `uvm_info(`gfn, $sformatf("received tl_unfilt item:\n%0s", item.sprint()), UVM_HIGH)
  end
endtask : process_tl_unfilt_fifo

task ac_range_check_scoreboard::process_tl_filt_fifo();
  tl_seq_item item;
  forever begin
    tl_filt_fifo.get(item);
    `uvm_info(`gfn, $sformatf("received tl_filt item:\n%0s", item.sprint()), UVM_HIGH)
  end
endtask : process_tl_filt_fifo

task ac_range_check_scoreboard::process_tl_access(tl_seq_item item,
                                                  tl_channels_e channel,
                                                  string ral_name);
  uvm_reg csr;
  bit     do_read_check   = 1'b1;
  bit     write           = item.is_write();
  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

  bit addr_phase_read   = (!write && channel == AddrChannel);
  bit addr_phase_write  = ( write && channel == AddrChannel);
  bit data_phase_read   = (!write && channel == DataChannel);
  bit data_phase_write  = ( write && channel == DataChannel);

  // If access was to a valid csr, get the csr handle
  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
  end else begin
    `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
  end

  // If incoming access is a write to a valid csr, then make updates right away
  if (addr_phase_write) begin
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
  end

  // Process the csr req:
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
    default: begin
      `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
    end
  endcase

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (data_phase_read) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask : process_tl_access

function void ac_range_check_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  // Reset local fifos queues and variables
endfunction : reset

function void ac_range_check_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  // Post test checks - ensure that all local fifos and queues are empty
endfunction : check_phase
