// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class i2c_host_rx_oversample_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_rx_oversample_vseq)

  constraint num_trans_c {
    num_trans == cfg.seq_cfg.i2c_max_num_trans;
  }

  class host_rx_oversample_timing_cfg extends i2c_timing_cfg;
    constraint oversample_c {
      tc.thigh   == 1;
      tc.t_r     == 1;
      tc.t_f     == 1;
      tc.thd_sta == 1;
      tc.tsu_sto == 1;
      tc.tsu_dat == 1;
      tc.thd_dat == 1;
    }
  endclass : host_rx_oversample_timing_cfg

  function new (string name="");
    host_rx_oversample_timing_cfg ostc = new;
    super.new(name);
    `downcast(tcc, ostc);
    // Disable the baseclass constraints which conflict with 'oversample_c'.
    tcc.timing_val_minmax_c.constraint_mode(0);
    tcc.implementation_c.constraint_mode(0);
    tcc.agent_c.constraint_mode(0);
  endfunction : new

  virtual task body();
    initialization();
    for(int i = 0; i < num_runs; i++) begin
      bit do_interrupt = 1'b1;
      `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
      fork
        begin
          while (!cfg.under_reset && do_interrupt) process_interrupts();
        end
        begin
          host_send_trans(num_trans);
          do_interrupt = 1'b0; // gracefully stop process_interrupts
        end
      join
      `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
    end
  endtask : body

endclass : i2c_host_rx_oversample_vseq
