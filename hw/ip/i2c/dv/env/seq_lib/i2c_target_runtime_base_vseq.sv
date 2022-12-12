// Copyright lowRISC contributors.
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
  // set this bit to 1 to stop reading acq fifo.
  // To resume read acq fifo, it has to be set to 0.
  bit pause_acq_read = 0;
  // 1 bit cycle : thigh + tlow
  // one acq entry can be popped every 9 bit cycles (8bit + ack)
  int acq_rd_cyc;
  i2c_target_base_seq m_i2c_host_seq;

  virtual task body();
    i2c_item txn_q[$];
    bit timer_expired = 0;

    initialization(Device);
    `uvm_info("cfg_summary", $sformatf("target_addr0:0x%x target_addr1:0x%x num_trans:%0d",
                             target_addr0, target_addr1, num_trans), UVM_MEDIUM)
    print_time_property();
    get_timing_values();
    program_registers();
    acq_rd_cyc = 9 * (thigh + tlow);
    fork
      begin
        fork
          while (timer_expired == 0) begin
            `JDBG(("assa: myseq begin"))
            `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
            create_txn(txn_q);
            fetch_txn(txn_q, m_i2c_host_seq.req_q);
            m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
            `JDBG(("assa: myseq end"))
            wait(pause_acq_read == 0);
          end
          process_target_interrupts();
        join
      end
      begin
        #(seq_runtime * 1us);
        `JDBG(("assa timer expred"))
        timer_expired = 1;
        cfg.stop_intr_handler = 1;
      end
      begin
        test_event();
      end
      begin
        process_acq();
      end
      begin
        process_txq();
      end
    join
  endtask
  virtual task test_event; endtask
  virtual task process_acq; endtask
  virtual task process_txq; endtask
endclass
