// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic error_intr test vseq
// - start sending transaction and concurrently check the occurance of error irqs
//   such as sda_interference, scl_interference, sda_unstable irqs
// - do on-the-fly reset dut and dv if error irqs are asserted
// - continue sending transactions and verify dut works as normal
class i2c_error_intr_vseq extends i2c_sanity_vseq;
  `uvm_object_utils(i2c_error_intr_vseq)
  `uvm_object_new

  bit do_reset = 1'b0;

  // increase num_trans to cover error interrupts
  constraint num_trans_c { num_trans inside {[50 : 100]}; }

  virtual task body();
    // allow agent/target creating interference and unstable signals so
    // sda_interference, scl_interference, sda_unstable are asserted
    cfg.en_sda_unstable     = 1'b1;
    cfg.en_sda_interference = 1'b1;
    cfg.en_scl_interference = 1'b1;

    device_init();
    host_init();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_resets)
    for (int run = 0; run < num_resets; run++) begin
      `uvm_info(`gfn, $sformatf("\n****** RUN %0d ******", run), UVM_DEBUG)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
      fork
        begin
          // issue trans. and check the occourances of error irqs
          fork
            begin
              process_error_interrupts();
              apply_reset("HARD");
              `uvm_info(`gfn, $sformatf("\n>>>Reset ended"), UVM_DEBUG)
            end
            host_send_trans(num_trans);
          join_any
          // stop all tl_seqs
          p_sequencer.tl_sequencer_h.stop_sequences();
          disable fork;
          // delay to avoid race condition when sending item and
          // checking no item after reset occur at the same time
          #1ps;
          // handle on-the-fly reset
          if (do_reset) begin
            host_init();
            do_reset = 1'b0;
          end
        end
      join
    end
  endtask : body

  virtual task process_error_interrupts();

    forever begin
      @(posedge cfg.clk_rst_vif.clk) begin
        if (cfg.intr_vif.pins[SclInference] ||
            cfg.intr_vif.pins[SdaInference] ||
            cfg.intr_vif.pins[SdaUnstable]) begin
          `uvm_info(`gfn, $sformatf("\n>>>Get error interrupts SclIrf %b, SdaIrf %b, SdaUns %b",
              cfg.intr_vif.pins[SclInference], cfg.intr_vif.pins[SdaInference],
              cfg.intr_vif.pins[SdaUnstable]), UVM_DEBUG)
          do_reset = 1'b1;
          break;
        end
      end
    end
  endtask : process_error_interrupts

endclass : i2c_error_intr_vseq
