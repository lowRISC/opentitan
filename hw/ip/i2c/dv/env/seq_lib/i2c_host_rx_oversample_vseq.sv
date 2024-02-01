// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class i2c_host_rx_oversample_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_rx_oversample_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans == cfg.seq_cfg.i2c_max_num_trans;
  }
  constraint timing_val_c {
    thigh   == 1;
    t_r     == 1;
    t_f     == 1;
    thd_sta == 3;
    tsu_sto == 1;
    tsu_dat == 1;
    thd_dat == 1;

    t_buf > thd_dat + 1;

    solve t_r, tsu_dat, thd_dat before tlow;
    solve t_r                   before t_buf;
    solve t_f, thigh            before t_sda_unstable, t_sda_interference;
    if (program_incorrect_regs) {
      // force derived timing parameters to be negative (incorrect DUT config)
      tsu_sta == t_r + t_buf + 1;  // negative tHoldStop
      tlow    == 2;                // negative tClockLow
      t_buf   == 2;
      t_sda_unstable     == 0;
      t_sda_interference == 0;
      t_scl_interference == 0;
    } else {
      tsu_sta inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
      // force derived timing parameters to be positive (correct DUT config)
      // This should be tied to 'get_timing_values' in i2c_base_vseq.sv
      // To avoid tClockLow 'min tlow should be greater than 5
      tlow    inside {[(t_r + tsu_dat + thd_dat + 2) :
                       (t_r + tsu_dat + thd_dat + 2) + cfg.seq_cfg.i2c_time_range]};
      t_buf   inside {[(tsu_sta - t_r + 1) :
                       (tsu_sta - t_r + 1) + cfg.seq_cfg.i2c_time_range]};
      t_sda_unstable     inside {[0 : t_r + thigh + t_f - 1]};
      t_sda_interference inside {[0 : t_r + thigh + t_f - 1]};
      t_scl_interference inside {[0 : t_r + thigh + t_f - 1]};
    }
  }

  virtual task body();
    initialization();
    print_time_property();
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
