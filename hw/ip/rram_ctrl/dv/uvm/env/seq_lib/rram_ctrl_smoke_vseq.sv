// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Minimal smoke test: brings the DUT out of reset (via dut_init()/rram_ctrl_init()) and does
// nothing else. Real content is still TODO(#31293) (writes, reads, host access, etc.).
class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  // The number of bus words to read/write/rewrite in SW operations
  int unsigned m_num_sw_words = 100;

  extern function new(string name="");
  extern task body();

  extern task dut_init(string reset_kind = "HARD");

  // Randomize the configuration of the regions and info pages
  extern local task randomize_cfg();
endclass : rram_ctrl_smoke_vseq

function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();
  rram_ctrl_sw_burst_vseq burst_vseq = rram_ctrl_sw_burst_vseq::type_id::create("burst_vseq");
  burst_vseq.set_ral(cfg.ral);
  burst_vseq.m_num_words = m_num_sw_words;

  if (!burst_vseq.randomize()) `uvm_fatal("failed_rand", "Failed to randomize burst_vseq.")

  fork : isolation_fork begin
    fork
      burst_vseq.start(null);
      begin
        wait(cfg.under_reset);
        burst_vseq.abort();
        wait(0);
      end
    join_any
    disable fork;
  end join

  // TODO(#31293): add real tests.
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
  rram_ctrl_randomize_vseq rand_vseq = rram_ctrl_randomize_vseq::type_id::create("rand_vseq");
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
endtask
