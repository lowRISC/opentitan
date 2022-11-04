// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Basic smoke test vseq
class i2c_target_smoke_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_target_smoke_vseq)
  `uvm_object_new

  int tran_id;

  int full_txn_num = 0;
  // Start counter including restart. Starting from 1 to match rtl value
  // and easy to trace.
  int start_cnt = 1;
  int exp_rd_id = 0;
  int exp_wr_id = 0;
  i2c_item read_txn_q[$];

  // This is only valid in target mode simulation
  int   i2c_csr_default_timeout = 10000; // 10us
  int   read_rcvd[$];

  virtual task body();
    i2c_target_base_seq m_i2c_host_seq;
    i2c_item txn_q[$];

    // Intialize dut in device mode and agent in host mode
    initialization(Device);
    `uvm_info("cfg_summary", $sformatf("target_addr0:0x%x target_addr1:0x%x num_trans:%0d",
                             target_addr0, target_addr1, num_trans), UVM_MEDIUM)
    print_time_property();

    fork
      begin
        for (int i = 0; i < num_trans; i++) begin
          get_timing_values();
          if (i > 0) begin
            // wait for previous stop before program a new timing param.
            @(cfg.m_i2c_agent_cfg.got_stop);
          end
          program_registers();

          `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
          create_txn(txn_q);
          fetch_txn(txn_q, m_i2c_host_seq.req_q);
          m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
        end
      end
      begin
        process_acq();
      end
      begin
        process_txq();
      end
    join_none
  endtask : body

  // Polling read_rcvd q and fetch read data to txdata fifo
  task process_txq();
    uvm_reg_data_t data;
    int read_size;
    int rd_txfifo_timeout_ns = 50_000;

    forever begin
      @(cfg.m_i2c_agent_cfg.vif.cb);
      if (read_rcvd.size() > 0) begin
        read_size = read_rcvd.pop_front();
      end
      while (read_size > 0) begin
        @(cfg.m_i2c_agent_cfg.vif.cb);
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
        end
      end
    end
  endtask

  function void create_txn(ref i2c_item myq[$]);
    bit [7:0] wdata_q[$];
    i2c_item txn;
    bit       rs_avl;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wdata_q,
                                       wdata_q.size() inside {
                           [cfg.min_data : cfg.max_data]};)

    for (int i = 0; i < wdata_q.size(); i++) begin
      if ($urandom_range(0,9) < cfg.rs_pct) rs_avl = 1;
      else rs_avl = 0;
      // restart entry
      if (rs_avl == 1 && i > 0) begin
        `uvm_info("seq", $sformatf("RS inserted before data %0d", i), UVM_MEDIUM)
        `uvm_create_obj(i2c_item, txn)
        txn.drv_type = HostRStart;
        txn.rstart = 1;
        txn.stop = 0;
        txn.read = get_read_write();
        myq.push_back(txn);
      end
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostData;
      txn.wdata = wdata_q[i];
      myq.push_back(txn);
    end
  endfunction

  task fetch_txn(ref i2c_item src_q[$], i2c_item dst_q[$]);
    i2c_item txn;
    i2c_item rs_txn;
    i2c_item exp_txn;
    i2c_item full_txn;
    int read_size;
    bit is_read = get_read_write();

    `uvm_info("seq", $sformatf("idx %0d:is_read:%0b size:%0d fetch_txn", start_cnt++, is_read,
                               src_q.size(), full_txn_num++), UVM_MEDIUM)
    print_wr_data(src_q);
    `uvm_create_obj(i2c_item, full_txn)

    // Add 'START' to the front
    `uvm_create_obj(i2c_item, txn)
    txn.drv_type = HostStart;
    dst_q.push_back(txn);
    full_txn.start = 1;
    if (is_read) full_txn.tran_id = this.exp_rd_id++;
    // Address
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.drv_type = HostData;
    txn.start = 1;
    txn.wdata[7:1] = target_addr0;
    txn.wdata[0] = is_read;
    txn.tran_id = this.tran_id++;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.addr = txn.wdata[7:1];
    full_txn.read = is_read;

    p_sequencer.target_mode_wr_exp_port.write(exp_txn);
    cfg.sent_acq_cnt++;

    if (is_read) begin
      read_size = src_q.size();
      read_rcvd.push_back(read_size);
    end
    // Data
    while (src_q.size() > 0) begin
      `uvm_create_obj(i2c_item, txn)
      txn = src_q.pop_front();
      if (txn.drv_type != HostRStart) begin
        // Restart only has empty data for address holder
        full_txn.data_q.push_back(txn.wdata);
      end

      // RS creates 2 extra acq entry
      // one for RS
      // the other for a new start acq_entry with address
      if (txn.drv_type == HostRStart) begin
        bit prv_read = 0;
        `uvm_create_obj(i2c_item, exp_txn)
        exp_txn.drv_type = HostRStart;
        exp_txn.rstart = 1;
        exp_txn.tran_id = this.tran_id++;
        p_sequencer.target_mode_wr_exp_port.write(exp_txn);
        cfg.sent_acq_cnt++;
        `uvm_create_obj(i2c_item, rs_txn)
        `downcast(rs_txn, txn.clone())
        dst_q.push_back(txn);

        rs_txn.drv_type = HostData;
        rs_txn.start = 1;
        rs_txn.rstart = 0;
        rs_txn.wdata[7:1] = target_addr1;
        prv_read = is_read;
        is_read = rs_txn.read;
        rs_txn.wdata[0] = is_read;
        dst_q.push_back(rs_txn);
        // create a separate stat/addr entry for exp
        `uvm_create_obj(i2c_item, exp_txn)
        `downcast(exp_txn, rs_txn.clone());
        exp_txn.tran_id = this.tran_id++;
        p_sequencer.target_mode_wr_exp_port.write(exp_txn);
        cfg.sent_acq_cnt++;
        // fetch previous full_txn and creat a new one
        if (prv_read) begin
          full_txn.stop = 1;
          p_sequencer.target_mode_rd_exp_port.write(full_txn);
        end
        `uvm_create_obj(i2c_item, full_txn)
        `downcast(full_txn, rs_txn);
        if (is_read) begin
          full_txn.tran_id = exp_rd_id++;
        end
      end else begin
        if (is_read) begin
          i2c_item read_txn;
          `uvm_create_obj(i2c_item, read_txn)
          `downcast(read_txn, txn.clone())
          full_txn.num_data++;
          if (src_q.size() == 0) begin
            txn.drv_type = HostNAck;
          end else begin
            // if your next item is restart Do nack
            if (src_q[0].drv_type == HostRStart) txn.drv_type = HostNAck;
            else txn.drv_type = HostAck;
          end
          dst_q.push_back(txn);
          read_txn_q.push_back(read_txn);
        end else begin
          `downcast(exp_txn, txn.clone());
          // Add RS transaction to driver only
          // and create address transaction after
          dst_q.push_back(txn);
          exp_txn.tran_id = this.tran_id++;
          p_sequencer.target_mode_wr_exp_port.write(exp_txn);
          cfg.sent_acq_cnt++;
        end
      end
    end // while (src_q.size() > 0)

    // Stop
    `uvm_create_obj(i2c_item, txn)
    `uvm_create_obj(i2c_item, exp_txn)
    txn.tran_id = this.tran_id++;
    txn.stop = 1;
    txn.drv_type = HostStop;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.stop = 1;
    p_sequencer.target_mode_wr_exp_port.write(exp_txn);
    cfg.sent_acq_cnt++;
    if (is_read) begin
      p_sequencer.target_mode_rd_exp_port.write(full_txn);
    end
  endtask

  task process_acq();
    uvm_reg_data_t read_data;
    i2c_item obs;
    bit is_read;

    wait(cfg.sent_acq_cnt > 0);

    while (cfg.sent_acq_cnt != cfg.rcvd_acq_cnt) begin
      // polling status.acqempty == 0
      csr_rd(.ptr(ral.status.acqempty), .value(read_data));
      if (read_data == 0) begin

        // read one entry and compare
        csr_rd(.ptr(ral.acqdata), .value(read_data));
        `uvm_info("process_acq", $sformatf("acq data %x", read_data), UVM_MEDIUM)
        `uvm_create_obj(i2c_item, obs);
        obs = acq2item(read_data);
        is_read = obs.read;

        obs.tran_id = cfg.rcvd_acq_cnt++;
        p_sequencer.target_mode_wr_obs_port.write(obs);
      end else begin // if (read_data == 0)
        cfg.clk_rst_vif.wait_clks(1);
        `uvm_info("process_acq", $sformatf("acq_dbg: sent:%0d rcvd:%0d acq_is_empty",
                                           cfg.sent_acq_cnt, cfg.rcvd_acq_cnt), UVM_HIGH)
      end
    end
  endtask

endclass : i2c_target_smoke_vseq
