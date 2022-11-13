// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_stress_rd_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stress_rd_vseq)
  `uvm_object_new

  constraint num_trans_c { num_trans inside {[1 : 5]}; }

  virtual task body();
    `uvm_info(`gfn, $sformatf("num_trans:%0d", num_trans), UVM_MEDIUM)

    cfg.min_data = 100;
    cfg.max_data = 200;
    cfg.wr_pct = 0;
    cfg.m_i2c_agent_cfg.use_seq_term = 1;
    do_clear_all_interrupts = 0;

    super.body();
  endtask // body

  task process_txq();
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 50_000;
    int tx_empty_timeout_ns = 100_000;

    int delay;

    wait(cfg.m_i2c_agent_cfg.sent_rd_byte > 0);

     while (cfg.m_i2c_agent_cfg.sent_rd_byte !=
           cfg.m_i2c_agent_cfg.rcvd_rd_byte ||
           sent_txn_cnt < num_trans) begin
        @(cfg.m_i2c_agent_cfg.vif.cb);

        if (read_rcvd.size() > 0) begin
           read_size = read_rcvd.pop_front();
        end
        delay = $urandom_range(5, 10);
        #(delay * 1us);

      while (read_size > 0) begin
        @(cfg.m_i2c_agent_cfg.vif.cb);
        if ($urandom_range(0, 1) < 1) begin
           // wait for intr_state.tx_empty
`JDBG(("assa proc_txq wait tx_empty"))
          csr_spinwait(.ptr(ral.intr_state.tx_empty), .exp_data(1'b1),
                       .timeout_ns(tx_empty_timeout_ns));
          csr_wr(.ptr(ral.intr_state.tx_empty), .value(1'b1));
        end
         if (read_txn_q.size() > 0) begin
          i2c_item item;
          //check tx fifo is full
          csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                       .timeout_ns(rd_txfifo_timeout_ns));
          `uvm_create_obj(i2c_item, item)
          item = read_txn_q.pop_front();
          `uvm_info("process_txq", $sformatf("send rdata:%x", item.wdata), UVM_MEDIUM)

          csr_wr(.ptr(ral.txdata), .value(item.wdata));
          read_size--;
//`JDBG(("assa proc_txq after txdata %0d", read_size))
        end
      end // while (read_size > 0)
//      `JDBG(("assa sent:%0d rcvd:%0d", cfg.m_i2c_agent_cfg.sent_rd_byte, cfg.m_i2c_agent_cfg.rcvd_rd_byte))
    end // while (cfg.m_i2c_agent_cfg.sent_byte !=...
     cfg.m_i2c_agent_cfg.use_seq_term = 0;
     `JDBG(("assa out"))
  endtask

endclass
