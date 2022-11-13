// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_target_stretch_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_stretch_vseq)
  `uvm_object_new

  bit wr_end = 0;
  bit rd_end = 0;
  bit got_read_cmd[$];
 
  constraint num_trans_c { num_trans inside {[1 : 5]}; }

  virtual task body();
     num_trans = 1;
 
    cfg.min_data = 100;
    cfg.max_data = 200;
    cfg.m_i2c_agent_cfg.use_seq_term = 1;
    do_clear_all_interrupts = 0;

    super.body();
  endtask // body
  // slow acq fifo read to create acq_fifo full
  task process_acq();
    uvm_reg_data_t read_data;
    i2c_item obs;
    bit is_read;
    bit acq_fifo_empty = 1;
    int delay;

    wait(cfg.sent_acq_cnt > 0);

    while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt ||
           acq_fifo_empty == 0) begin

      delay = $urandom_range(50, 100);

      // Assuming interval between each byte is 6.2us
      #(delay * 1us);

      // polling status.acqempty == 0
      csr_rd(.ptr(ral.status.acqempty), .value(acq_fifo_empty));

      if (!acq_fifo_empty) begin

        // read one entry and compare
        csr_rd(.ptr(ral.acqdata), .value(read_data));
        `uvm_info("process_acq", $sformatf("acq data %x", read_data), UVM_MEDIUM)
        `uvm_create_obj(i2c_item, obs);
        obs = acq2item(read_data);
	if ( (obs.start | obs.rstart) & obs.read) begin
	   got_read_cmd.push_back(1);
`JDBG(("assa proc_acq got read"))	   
	end
//        is_read = obs.read;

        obs.tran_id = cfg.rcvd_acq_cnt++;
        p_sequencer.target_mode_wr_obs_port.write(obs);
      end else begin // if (read_data == 0)
        cfg.clk_rst_vif.wait_clks(1);
        `uvm_info("process_acq", $sformatf("acq_dbg: sent:%0d rcvd:%0d acq_is_empty",
                                           cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_MEDIUM)
      end
    end // while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt ||...
    wr_end = 1;
     `JDBG(("assa out1"))
     
//    cfg.m_i2c_agent_cfg.use_seq_term = 0;
    `uvm_info("process_acq", "use_seq_item is off", UVM_MEDIUM)
  endtask

  task process_txq();
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 50_000;
    // indefinite time
    int tx_empty_timeout_ns = 500_000_000;

    int delay;
    bit dummy;
     
    wait(cfg.m_i2c_agent_cfg.sent_rd_byte > 0);

     while (cfg.m_i2c_agent_cfg.sent_rd_byte !=
           cfg.m_i2c_agent_cfg.rcvd_rd_byte ||
           sent_txn_cnt < num_trans) begin
        @(cfg.m_i2c_agent_cfg.vif.cb);
// 	wait(got_read_cmd.size > 0);
// 	dummy = got_read_cmd.pop_front();
//`JDBG(("assa proc_txq got read cmd"))	
        if (read_rcvd.size() > 0) begin
           read_size = read_rcvd.pop_front();
`JDBG(("assa proc_txq read_size :%0d ", read_size))	   
        end
//        delay = $urandom_range(5, 10);
//        #(delay * 1us);

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
`JDBG(("assa proc_txq after txdata %0d", read_size))
        end
      end // while (read_size > 0)
//      `JDBG(("assa sent:%0d rcvd:%0d", cfg.m_i2c_agent_cfg.sent_rd_byte, cfg.m_i2c_agent_cfg.rcvd_rd_byte))
    end // while (cfg.m_i2c_agent_cfg.sent_byte !=...


    rd_end = 1;
    wait (wr_end == 1);
     cfg.m_i2c_agent_cfg.use_seq_term = 0;
     `JDBG(("assa out2"))
  endtask

endclass // i2c_target_stretch_vseq
