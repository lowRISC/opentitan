// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_i2c_device_tx_rx_vseq extends chip_sw_i2c_tx_rx_vseq;
  `uvm_object_utils(chip_sw_i2c_device_tx_rx_vseq)

  `uvm_object_new

  int exp_rd_id = 0;
  int tran_id = 0;
  i2c_item read_txn_q[$];

  rand int i2c_idx;
  constraint i2c_idx_c {
    i2c_idx == 0;
  }

  rand int byte_count;
  constraint i2c_byte_count_c {
    byte_count inside {[30:60]};
  }

  rand bit [6:0] i2c_device_address_0;
  rand bit [6:0] i2c_device_address_1;

  virtual task cpu_init();
    bit[7:0] clock_period_nanos_arr[1] = {clock_period_nanos};
    bit[7:0] rise_fall_nanos_arr[1] = {rise_fall_nanos};
    bit[7:0] i2c_clock_period_nanos_arr[4] = {<<byte{i2c_clock_period_nanos}};
    bit[7:0] i2c_idx_arr[1];
    bit[7:0] i2c_device_address_0_arr[1];
    bit[7:0] i2c_device_address_1_arr[1];
    bit[7:0] byte_count_arr[1];

    void'($value$plusargs("i2c_idx=%0d", i2c_idx));
    `DV_CHECK(i2c_idx inside {[0:NUM_I2CS-1]})

    i2c_idx_arr = {i2c_idx};
    i2c_device_address_0_arr = {i2c_device_address_0};
    i2c_device_address_1_arr = {i2c_device_address_1};
    byte_count_arr = {byte_count};
    super.cpu_init();
    // need to figure out a better way to calculate this based on tb clock frequency
    sw_symbol_backdoor_overwrite("kClockPeriodNanos", clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cRiseFallNanos", rise_fall_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cClockPeriodNanos", i2c_clock_period_nanos_arr);
    // sw_symbol_backdoor_overwrite("kI2cIdx", i2c_idx_arr);
    sw_symbol_backdoor_overwrite("kI2cDeviceAddress0", i2c_device_address_0_arr);
    // sw_symbol_backdoor_overwrite("kI2cDeviceMask0", i2c_device_mask_0);
    sw_symbol_backdoor_overwrite("kI2cDeviceAddress1", i2c_device_address_1_arr);
    // sw_symbol_backdoor_overwrite("kI2cDeviceMask1", i2c_device_mask_1);
    sw_symbol_backdoor_overwrite("kI2cByteCount", byte_count_arr);
    // sw_symbol_backdoor_overwrite("expected_data", i2c_device_tx_data);
  endtask

  virtual task body();
    bit [7:0] i2c_device_tx_data[$];
    super.body();

    // enable the monitor
    cfg.m_i2c_agent_cfgs[i2c_idx].en_monitor = 1'b1;
    cfg.m_i2c_agent_cfgs[i2c_idx].if_mode = Host;

    // Enbale appropriate interface
    cfg.chip_vif.enable_i2c(.inst_num(i2c_idx), .enable(1));

    // tClockLow needs to be "slightly" shorter than the actual clock low period
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockLow = half_period_cycles - 2;

    // tClockPulse needs to be "slightly" longer than the clock period.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockPulse = half_period_cycles + 1;

    // tHoldStart and tClockStart need to be non-zero to make the start condition detectable.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldStart = half_period_cycles;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockStart = half_period_cycles;

    // tClockStop, tSetupStop, and tHoldStop have to be non-zero to make the stop condition
    // detectable.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockStop = half_period_cycles;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupStop = half_period_cycles - 2;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldStop = half_period_cycles;

    // Wait for i2c_device to fill tx_fifo
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Data written to fifo");

    send_i2c_host_rx_data(i2c_device_tx_data, byte_count);

  endtask

  virtual task send_i2c_host_rx_data(ref bit [7:0] device_data[$],input int size);
    i2c_target_base_seq m_i2c_host_seq;
    i2c_item txn_q[$];
    `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
    create_txn(txn_q, size);
    fetch_txn(txn_q, m_i2c_host_seq.req_q, .is_read(1));
    m_i2c_host_seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]);

    // Wait for reads to complete.
    `DV_WAIT(cfg.m_i2c_agent_cfgs[i2c_idx].sent_rd_byte > 0)
    `DV_WAIT(cfg.m_i2c_agent_cfgs[i2c_idx].sent_rd_byte ==
             cfg.m_i2c_agent_cfgs[i2c_idx].rcvd_rd_byte)
    `uvm_info(`gfn, "Reads complete.", UVM_MEDIUM)

    // Play transactions back.
    txn_q.delete();
    while (p_sequencer.i2c_rd_fifos[i2c_idx].can_get()) begin
      i2c_item txn;
      `DV_CHECK(p_sequencer.i2c_rd_fifos[i2c_idx].try_get(txn))
      foreach (txn.data_q[i]) begin
        i2c_item wr_txn;
        `uvm_create_obj(i2c_item, wr_txn)
        wr_txn.drv_type = HostData;
        wr_txn.wdata = txn.data_q[i];
        txn_q.push_back(wr_txn);
      end
    end
    fetch_txn(txn_q, m_i2c_host_seq.req_q, .is_read(0));
    m_i2c_host_seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]);
  endtask

  // Create byte transaction (payload) to read or write.
  // Transaction type (read, write) is decided in 'fetch_txn'.
  // This function and `fetch_txn` are largely duplicates of the code in `i2c_base_vseq`, so at
  // some point it may be worth refactoring the common parts into a separate class or package to
  // deduplicate code.
  virtual function void create_txn(ref i2c_item myq[$], int num_bytes);
    bit [7:0] wdata_q[$];
    i2c_item  txn;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wdata_q,
                                       wdata_q.size() == num_bytes;)

    for (int i = 0; i < wdata_q.size(); i++) begin
      `uvm_create_obj(i2c_item, txn)
      txn.drv_type = HostData;
      txn.wdata = wdata_q[i];
      myq.push_back(txn);
    end
  endfunction

  // Receive byte stream from 'create_txn' and forward to driver's request q,
  // with adding 'Start and Stop'.
  // Expected transaction is created in the task.
  // For write transaction and address transaction, expected transaction mimics acq read data.
  // For read transaction, all read bytes for one transaction is accumulated to 'full_txn'
  // and compared with received transaction at the scoreboard.
  virtual function void fetch_txn(ref i2c_item src_q[$], i2c_item dst_q[$], input bit is_read);
    i2c_item txn;
    i2c_item rs_txn;
    i2c_item exp_txn;
    i2c_item full_txn;
    int read_size;

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
    txn.wdata[7:1] = i2c_device_address_0;
    txn.wdata[0] = is_read;
    txn.tran_id = this.tran_id++;
    `downcast(exp_txn, txn.clone());
    dst_q.push_back(txn);
    full_txn.addr = txn.wdata[7:1];
    full_txn.read = is_read;

    read_size = byte_count;
    cfg.m_i2c_agent_cfgs[i2c_idx].sent_rd_byte += read_size;

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

        `uvm_create_obj(i2c_item, rs_txn)
        `downcast(rs_txn, txn.clone())
        dst_q.push_back(txn);

        rs_txn.drv_type = HostData;
        rs_txn.start = 1;
        rs_txn.rstart = 0;
        rs_txn.wdata[7:1] = i2c_device_address_0;
        prv_read = is_read;
        is_read = rs_txn.read;
        rs_txn.wdata[0] = is_read;
        dst_q.push_back(rs_txn);
        // create a separate stat/addr entry for exp
        `uvm_create_obj(i2c_item, exp_txn)
        `downcast(exp_txn, rs_txn.clone());
        exp_txn.tran_id = this.tran_id++;

        // fetch previous full_txn and creat a new one
        if (prv_read) begin
          full_txn.stop = 1;
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
  endfunction


endclass : chip_sw_i2c_device_tx_rx_vseq
