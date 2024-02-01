// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base sequence for any data path drop test for target_mode i2c.
// Random data path drop event make difficult to predict sent/rcvd counter.
// This base sequence run the sequence for 'seq_runtime' and
// test execution does not rely on sent / rcvd counter.
class i2c_target_runtime_base_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_runtime_base_vseq)
  `uvm_object_new

  // sequence running time in us
  // update this value using 'pre_start' in child sequence.
  int seq_runtime = 0;
  // set this bit to 1 to hold next sequence start.
  bit pause_seq = 0;
  // 1 bit cycle : thigh + tlow
  // one acq entry can be popped every 9 bit cycles (8bit + ack)
  int acq_rd_cyc;
  i2c_target_base_seq m_i2c_host_seq;

  virtual task body();
    i2c_item txn_q[$];
    bit timer_expired = 0;

    initialization();
    `uvm_info("cfg_summary", $sformatf("target_addr0:0x%x target_addr1:0x%x num_trans:%0d",
                             target_addr0, target_addr1, num_trans), UVM_MEDIUM)
    acq_rd_cyc = 9 * (thigh + tlow);
    fork
      begin
        fork
          while (timer_expired == 0) begin
            `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
            create_txn(txn_q);
            fetch_txn(txn_q, m_i2c_host_seq.req_q);
            m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
            `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop, "got_stop wait timeout occurred!",
                     cfg.spinwait_timeout_ns, "target_runtime_base_vseq")
            cfg.m_i2c_agent_cfg.got_stop = 0;
            // To avoid race between 'pause_seq set' and
            // 'cfg.m_i2c_agent_cfg.got_stop = 1'
            cfg.clk_rst_vif.wait_clks(1);
            `DV_WAIT(pause_seq == 0, "pause_seq == 0 wait timeout occurred!",
                     cfg.spinwait_timeout_ns, "target_runtime_base_vseq")
          end
          process_target_interrupts();
        join
      end
      begin
        #(seq_runtime * 1us);
        `uvm_info("seq", "timer expired", UVM_MEDIUM)
        timer_expired = 1;
        `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop, "got_stop wait timeout occurred!",
                 cfg.spinwait_timeout_ns, "target_runtime_base_vseq")
        cfg.stop_intr_handler = 1;
      end
      begin
        test_event();
      end
      begin
        process_acq();
      end
    join
  endtask
  virtual task test_event; endtask
  virtual task process_acq; endtask

  // If txfifo is not full,
  // fill random size of tx data upon receiving txstretch interrupt.
  // expected data will be stored at the scoreboard
  task proc_intr_txstretch();
    bit [7:0] wdata;
    int       lvl;
    int       delay;
    uvm_reg_data_t data;
    delay = $urandom_range(0, 10);
    cfg.clk_rst_vif.wait_clks(delay * acq_rd_cyc);
    csr_rd(.ptr(ral.target_fifo_status.txlvl), .value(data));
    data = 64 - data;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lvl, lvl dist {[1:16] := 7, [17:63] := 1, 64 := 2};)
    if (lvl > data) lvl = data;

    repeat (lvl) begin
      wdata = $urandom();
      csr_wr(.ptr(ral.txdata), .value(wdata));
    end
    clear_interrupt(TxStretch, 0);
  endtask // proc_intr_txstretch
endclass
