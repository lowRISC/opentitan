// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// performance test vseq
class i2c_perf_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_perf_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[10 : 16]}; }

  // should have few long transactions
  constraint num_wr_bytes_c {
    num_wr_bytes dist {
      1       :/ 15,
      [2:8]   :/ 20,
      [9:32]  :/ 15,
      256     :/ 50
    };
  }
  // num_rd_bytes = 1: read transaction length is 256b bytes
  constraint num_rd_bytes_c {
    num_rd_bytes dist {
      0       :/ 50,
      1       :/ 15,
      [2:8]   :/ 20,
      [9:32]  :/ 15
    };
  }
  
  // clear interrupt immediately
  constraint clear_intr_dly_c { clear_intr_dly == 0; }
  
  // zero fifo access latency
  constraint fmt_fifo_access_dly_c { fmt_fifo_access_dly == 0;}
  constraint rx_fifo_access_dly_c  { rx_fifo_access_dly  == 0;}

  // fast timing values programmed to registers
  constraint timing_val_c {
    thigh     == 1;
    t_r       == 1;
    t_f       == 1;
    thd_sta   == 1;
    tsu_sto   == 1;
    tsu_dat   == 1;
    thd_dat   == 1;
    t_timeout == 1;
    e_timeout == 1;
    tsu_sta   == 1;
    tlow      == 4;  // min:  (t_r + tsu_dat + thd_dat + 1)
    t_buf     == 1;  // min:  (tsu_sta - t_r + 1)
  }

  task body();
    device_init();
    host_init();

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_trans)
    fork
      begin
        while (do_interrupt) process_interrupts();
      end
      begin
        host_send_trans(num_trans);
        do_interrupt = 1'b0; // gracefully stop process_interrupts
      end
    join
  endtask : body

endclass : i2c_perf_vseq

