// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic error_intr test vseq
// - start sending transaction and concurrently check the occurance of error irqs
//   such as sda_interference, scl_interference, sda_unstable irqs
// - do on-the-fly reset dut and dv if error irqs are asserted
// - continue sending transactions and verify dut works as normal
class i2c_host_error_intr_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_error_intr_vseq)
  `uvm_object_new

  local bit do_reset = 1'b0;

  // increase num_trans to cover error interrupts
  constraint num_trans_c { num_trans inside {[40 : 50]}; }

  virtual task pre_start();
    super.pre_start();
    // allow agent/target creating interference and unstable signals so
    // sda_interference, scl_interference, sda_unstable are asserted
    cfg.seq_cfg.en_sda_unstable     = 1'b1;
    cfg.seq_cfg.en_sda_interference = 1'b1;
    cfg.seq_cfg.en_scl_interference = 1'b1;
    print_seq_cfg_vars("pre-start");
  endtask : pre_start

  virtual task body();
    `uvm_info(`gfn, "\n--> start of i2c_host_error_intr_vseq", UVM_DEBUG)
    $assertoff(0, "tb.dut.i2c_core.u_i2c_fsm.SclInputGlitch_A");
    initialization();
    for (int i = 1; i <= num_runs; i++) begin
      `uvm_info(`gfn, $sformatf("\n  run simulation %0d/%0d", i, num_runs), UVM_DEBUG)
      fork
        begin
          // issue trans. and check the occourances of error irqs
          fork
            begin
              process_error_interrupts();
              apply_reset("HARD");
              `uvm_info(`gfn, $sformatf("\n  reset is issued within error_intr_vseq"), UVM_LOW)
            end
            begin
              host_send_trans(num_trans);
              // if host_send_trans is ended within apply_reset then
              // wait reset completed before ending fork...join_any
              wait(!cfg.under_reset);
            end
          join_any
          // stop all tl_seqs if reset is issued
          p_sequencer.tl_sequencer_h.stop_sequences();
          disable fork;
          // delay to avoid race condition when sending item and
          // checking no item after reset occur at the same time
          #1ps;
          if (do_reset) begin
            // re-initialize dut after on-the-fly reset
            initialization();
            do_reset = 1'b0;
          end
        end
      join
    end
    `uvm_info(`gfn, "\n--> end of i2c_host_error_intr_vseq", UVM_DEBUG)
  endtask : body

  virtual task process_error_interrupts();
    forever begin
      @(posedge cfg.clk_rst_vif.clk) begin
        if (cfg.intr_vif.pins[SclInference] ||
            cfg.intr_vif.pins[SdaInference] ||
            cfg.intr_vif.pins[SdaUnstable]) begin
          `uvm_info(`gfn, $sformatf("\n  get error interrupts SclIrf %b, SdaIrf %b, SdaUns %b",
              cfg.intr_vif.pins[SclInference], cfg.intr_vif.pins[SdaInference],
              cfg.intr_vif.pins[SdaUnstable]), UVM_DEBUG)
          do_reset = 1'b1;
          if (do_reset)
            `uvm_info(`gfn, $sformatf("\n  get error interrupts, do_reset %b", do_reset), UVM_LOW);
          break;
        end
      end
    end
  endtask : process_error_interrupts

endclass : i2c_host_error_intr_vseq
