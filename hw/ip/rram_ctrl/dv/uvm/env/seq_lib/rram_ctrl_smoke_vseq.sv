// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stimulus for a minimal smoke test.
//
//  - Initialises rram_ctrl (in rram_ctrl_base_vseq::dut_init)
//  - Configures a randomised set of regions and info page permissions
//  - Performs randomised allowed SW operations using rram_ctrl_sw_burst_vseq
//  - In parallel with these, requests data through host_tl with rram_ctrl_host_burst_vseq

class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  // The number of bus words to read/write/rewrite in SW operations
  int unsigned m_num_sw_words = 100;

  // The number of host_tl operations (data reads and fetches) to run
  int unsigned m_num_host_ops = 100;

  // Should the EXEC register be configured to allow fetches through the host_tl interface? If so,
  // this will be configured in dut_init (called by pre_start) and the virtual sequence that body
  // starts to perform host_tl accesses will contain some fetches.
  rand bit     m_allow_fetches;

  // The value that is written to the EXEC register (either ExecEn or something else, depending on
  // whether m_allow_fetches is set).
  rand bit [31:0] m_exec_val;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);
  extern task body();

  extern task dut_init(string reset_kind = "HARD");

  // Randomize the configuration of the regions and info pages
  extern local task randomize_cfg();

  // m_exec_val should either be ExecEn (if m_allow_fetches is true) or a different value (if not).
  extern constraint exec_val_c;
endclass : rram_ctrl_smoke_vseq

function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_smoke_vseq::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_field_int("m_num_sw_words", m_num_sw_words, 32);
  printer.print_field_int("m_num_host_ops", m_num_host_ops, 32);
  printer.print_field_int("m_allow_fetches", m_allow_fetches, 1);
  printer.print_field_int("m_exec_val", m_exec_val, 32);
endfunction

task rram_ctrl_smoke_vseq::body();
  rram_ctrl_sw_burst_vseq   sw_vseq;
  rram_ctrl_host_burst_vseq host_vseq;

  sw_vseq = rram_ctrl_sw_burst_vseq::type_id::create("sw_vseq");
  sw_vseq.set_ral(cfg.ral);
  sw_vseq.m_num_words = m_num_sw_words;
  if (!sw_vseq.randomize()) `uvm_fatal("failed_rand", "Failed to randomize sw_vseq.")

  host_vseq = rram_ctrl_host_burst_vseq::type_id::create("host_vseq");
  host_vseq.set_ral(cfg.ral);
  host_vseq.set_host_base_addr(cfg.ral_models[cfg.host_ral_name].get_default_map().get_base_addr());
  host_vseq.set_host_sequencer(p_sequencer.tl_sequencer_hs[cfg.host_ral_name]);
  host_vseq.m_num_ops = m_num_host_ops;
  host_vseq.m_allow_fetches = m_allow_fetches;

  if (!host_vseq.randomize()) `uvm_fatal("failed_rand", "Failed to randomize host_vseq.")

  // Run sw_vseq and host_vseq alongside each other. If reset is asserted, the wait will complete
  // and we will tell sw_vseq and host_vseq to abort.
  fork : isolation_fork begin
    fork
      fork
        sw_vseq.start(null);
        host_vseq.start(null);
      join
      begin
        wait(cfg.under_reset);
        sw_vseq.abort();
        host_vseq.abort();
        wait(0);
      end
    join_any
    disable fork;
  end join
endtask

task rram_ctrl_smoke_vseq::dut_init(string reset_kind = "HARD");
  fork
    super.dut_init(reset_kind);
    begin
      // Wait until the base class dut_init has applied any reset it intends to apply, then wait
      // until the reset is no longer applied. The 100 cycle wait here is to make sure we don't
      // start writing to registers just before the reset is applied.
      cfg.clk_rst_vif.wait_clks(100);

      // By this point, the reset will have been applied. In case it hasn't yet finished, wait until
      // the block is not in reset.
      wait(!cfg.under_reset);

      // At this point, we can sensibly randomise the configuration. This will be *much* quicker
      // than the wait for initialisation in rram_ctrl_init (which super.dut_init is waiting for).
      randomize_cfg();
    end
  join
endtask

task rram_ctrl_smoke_vseq::randomize_cfg();
  rram_ctrl_randomize_vseq rand_vseq;
  uvm_status_e             txn_status;

  // Create a sequence that will randomise the region and info page settings
  rand_vseq = rram_ctrl_randomize_vseq::type_id::create("rand_vseq");
  rand_vseq.set_ral(ral);

  if (!rand_vseq.randomize()) begin
    `uvm_fatal("failed_rand", "Failed to randomize rand_vseq.")
  end

  rand_vseq.start(null);
  if (cfg.under_reset) return;

  // We aren't under reset. If anything failed in setting the config registers, report the failure.
  if (rand_vseq.m_status != UVM_IS_OK) begin
    `uvm_error("failed_cfg_setting", "Error when setting config registers.")
  end

  // Write to the EXEC register to control whether fetches through host_tl are allowed
  ral.exec.write(txn_status, m_exec_val);
  if (cfg.under_reset) return;

  if (txn_status != UVM_IS_OK) begin
    `uvm_error("failed_reg_write", "Error when writing to EXEC register.")
  end
endtask

constraint rram_ctrl_smoke_vseq::exec_val_c {
  // Pick whether to allow fetches before picking the encoding. This avoids the disabled
  // configuration having probability 2^32-1 times as big as the enabled one.
  solve m_allow_fetches before m_exec_val;

  m_allow_fetches == (m_exec_val == rram_ctrl_reg_pkg::ExecEn);
}
