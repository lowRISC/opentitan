// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic smoke test vseq
class i2c_target_smoke_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_target_smoke_vseq)
  `uvm_object_new

  typedef i2c_item item_q[$];
  item_q txn_stimulus[int];

  constraint timing_val_c {
    thigh   inside {[                         4 : cfg.seq_cfg.i2c_max_timing]};
    t_r     inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    t_f     inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    thd_sta inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    tsu_sto inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    tsu_dat inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};
    thd_dat inside {[cfg.seq_cfg.i2c_min_timing : cfg.seq_cfg.i2c_max_timing]};

    solve t_r, tsu_dat, thd_dat before tlow;
    solve t_r                   before t_buf;
    solve tsu_sta               before t_buf;
    solve t_f, thigh            before t_sda_unstable, t_sda_interference;

    thd_sta > thd_dat + 1;
    t_buf > thd_dat + 1;

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
      // If we are generating a fixed_period SCL in the agent, we need the clock pulses
      // to be at-least long enough to contain an RSTART condition to chain transfers
      // together.
      thigh >= tsu_sta + t_f + thd_sta; // RSTART constraint
      // force derived timing parameters to be positive (correct DUT config)
      // tlow must be at least 2 greater than the sum of t_r + tsu_dat + thd_dat
      // because the flopped clock (see #15003 below) reduces tClockLow by 1.
      tlow    inside {[(t_r + tsu_dat + thd_dat + 5) :
                       (t_r + tsu_dat + thd_dat + 5) + cfg.seq_cfg.i2c_time_range]};
      t_buf   inside {[(tsu_sta - t_r + 1) :
                       (tsu_sta - t_r + 1) + cfg.seq_cfg.i2c_time_range]};
      t_sda_unstable     inside {[0 : t_r + thigh + t_f - 1]};
      t_sda_interference inside {[0 : t_r + thigh + t_f - 1]};
      t_scl_interference inside {[0 : t_r + thigh + t_f - 1]};
      // tHoldStop must be at least 2 cycles which implies, t_r + t_buf - tsu_sta >= 2
      // in order for stop condition to propogate to internal FSM via prim flop
      t_buf >= tsu_sta - t_r + 2;
    }
  }

  virtual task pre_start();
    super.pre_start();
    if (cfg.use_intr_handler) begin
      // Without populating the FMT FIFO its threshold interrupt will remain asserted.
      expected_intr[FmtThreshold] = 1;
      expected_intr[TxThreshold] = 1;
      expected_intr[AcqThreshold] = 1;
      expected_intr[AcqFull] = 1;
      expected_intr[TxStretch] = 1;
      expected_intr[CmdComplete] = 1;
      for (int i = 0; i < NumI2cIntr; i++) intr_q.push_back(i2c_intr_e'(i));
    end
    if (cfg.bad_addr_pct > 0) cfg.m_i2c_agent_cfg.allow_bad_addr = 1;
  endtask

  virtual task body();
    i2c_target_base_seq m_i2c_host_seq;

    `uvm_info(`gfn, $sformatf("num_trans:%0d", num_trans), UVM_MEDIUM)
    // Intialize dut in device mode and agent in host mode
    initialization();
    `uvm_info("cfg_summary",
              $sformatf("target_addr0:0x%x target_addr1:0x%x illegal_addr:0x%x num_trans:%0d",
                             target_addr0, target_addr1, illegal_addr, num_trans), UVM_MEDIUM)

    fork
      begin
        for (int i = 0; i < num_trans; i++) begin
          item_q txn_q;
          // Generate all the transactions up-front
          create_txn(txn_q);
          fetch_txn(txn_q, txn_stimulus[i]);
        end
        for (int i = 0; i < num_trans; i++) begin
          get_timing_values();
          if (i > 0) begin
            // wait for previous stop before program a new timing param.
            `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop,, cfg.spinwait_timeout_ns, "target_smoke_vseq")
            cfg.m_i2c_agent_cfg.got_stop = 0;
          end
          program_registers();

          `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
          m_i2c_host_seq.req_q = txn_stimulus[i];
          m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
          sent_txn_cnt++;
        end
      end
      begin
        if (!cfg.use_intr_handler) process_acq();
      end
      begin
        if (cfg.use_intr_handler == 1'b0 && cfg.rd_pct != 0) process_txq();
      end
      begin
        if (cfg.use_intr_handler) process_target_interrupts();
      end
      begin
        if (cfg.use_intr_handler) stop_target_interrupt_handler();
      end
    join
  endtask : body

endclass : i2c_target_smoke_vseq
