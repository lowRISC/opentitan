// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic smoke test vseq
class i2c_target_smoke_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_target_smoke_vseq)
  `uvm_object_new

  typedef i2c_item item_q[$];
  item_q txn_stimulus[int];

  virtual task pre_start();
    super.pre_start();
    if (cfg.use_intr_handler) begin
      // Without populating the FMT FIFO its threshold interrupt will remain asserted.
      expected_intr[FmtThreshold] = 1;
      expected_intr[TxThreshold] = 1;
      expected_intr[AcqThreshold] = 1;
      expected_intr[AcqStretch] = 1;
      expected_intr[TxStretch] = 1;
      expected_intr[CmdComplete] = 1;
      for (int i = 0; i < NumI2cIntr; i++) intr_q.push_back(i2c_intr_e'(i));
      cfg.ack_ctrl_en = $urandom_range(0, 1);
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
    `uvm_info(`gfn, $sformatf("ack_ctrl_en:%0d", cfg.ack_ctrl_en), UVM_MEDIUM);

    fork
      begin
        for (int i = 0; i < num_trans; i++) begin
          item_q txn_q;
          // Generate all the transactions up-front
          create_txn(txn_q);
          fetch_txn(txn_q, txn_stimulus[i]);
        end
        for (int i = 0; i < num_trans; i++) begin
          if (i > 0) begin
            // wait for previous stop before program a new timing param.
            `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop,, cfg.spinwait_timeout_ns, "target_smoke_vseq")
            cfg.m_i2c_agent_cfg.got_stop = 0;
          end
          program_registers(tcc.tc);

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
