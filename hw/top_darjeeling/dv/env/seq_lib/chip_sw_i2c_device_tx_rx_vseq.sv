// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// By default this test will use a randomly selected instance i2c_idx.
// To make a dedicated test for instance i, where i is in {0,1,2}, the test
// shuld run with an option:
//     run_opts: ["+i2c_idx=i"]

class chip_sw_i2c_device_tx_rx_vseq extends chip_sw_i2c_tx_rx_vseq;

  typedef i2c_item i2c_transfer_q[$];
  typedef i2c_transfer_q i2c_transaction;

  ///////////////
  // VARIABLES //
  ///////////////

  int tran_id = 0;

  rand bit [6:0] i2c_device_address_0;
  rand bit [6:0] i2c_device_address_1;
  rand bit [6:0] i2c_device_mask_0;
  rand bit [6:0] i2c_device_mask_1;
  rand bit       choose_address;
  rand bit [6:0] r;

  rand int i2c_idx;
  rand int byte_count;

  `uvm_object_utils(chip_sw_i2c_device_tx_rx_vseq)
  `uvm_object_new

  /////////////////
  // CONSTRAINTS //
  /////////////////

  constraint i2c_idx_c {
    i2c_idx inside {[0 : NUM_I2CS-1]};
  }

  constraint i2c_byte_count_c {
    byte_count inside {[30 : 60]};
  }

  /////////////
  // METHODS //
  /////////////

  // Override the base-class impl to pass software backdoor symbols that configure the DUT via SW.
  // - The I2C peripheral instance to test is selected via the plusarg '+i2c_idx'
  // - The timing parameters are taken from static values inherited from 'chip_sw_i2c_tx_rx_vseq'
  virtual task cpu_init();
    bit[7:0] clock_period_nanos_arr[1] = {clock_period_nanos};
    bit[7:0] rise_fall_nanos_arr[1] = {rise_fall_nanos};
    bit[7:0] i2c_clock_period_nanos_arr[4] = {<<byte{i2c_clock_period_nanos}};
    bit[7:0] i2c_idx_arr[1];

    bit[7:0] i2c_device_address_0_arr[1]  = {i2c_device_address_0};
    bit[7:0] i2c_device_address_1_arr[1] = {i2c_device_address_1};
    // if an address bit is 1, the corresponding mask bit must also be 1
    bit[7:0] i2c_device_mask_0_arr[1] = {i2c_device_address_0 | i2c_device_mask_0};
    bit[7:0] i2c_device_mask_1_arr[1] = {i2c_device_address_1 | i2c_device_mask_1};
    bit[7:0] byte_count_arr[1] = {byte_count};

    void'($value$plusargs("i2c_idx=%0d", i2c_idx));
    `DV_CHECK(i2c_idx inside {[0 : NUM_I2CS-1]})

    i2c_idx_arr = {i2c_idx};

    super.cpu_init();

    // Pass the symbols to test software via the backdoor

    sw_symbol_backdoor_overwrite("kClockPeriodNanos", clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cRiseFallNanos", rise_fall_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cClockPeriodNanos", i2c_clock_period_nanos_arr);
    sw_symbol_backdoor_overwrite("kI2cIdx", i2c_idx_arr);
    sw_symbol_backdoor_overwrite("kI2cDeviceAddress0", i2c_device_address_0_arr);
    sw_symbol_backdoor_overwrite("kI2cDeviceMask0", i2c_device_mask_0_arr);
    sw_symbol_backdoor_overwrite("kI2cDeviceAddress1", i2c_device_address_1_arr);
    sw_symbol_backdoor_overwrite("kI2cDeviceMask1", i2c_device_mask_1_arr);
    sw_symbol_backdoor_overwrite("kI2cByteCount", byte_count_arr);
  endtask

  virtual task body();
    super.body();

    // Enable the appropriate monitor
    cfg.m_i2c_agent_cfgs[i2c_idx].en_monitor = 1'b1;
    cfg.m_i2c_agent_cfgs[i2c_idx].if_mode = Host;

    // Enable appropriate interface
    cfg.chip_vif.enable_i2c(.inst_num(i2c_idx), .enable(1));

    // Configure the I2C Agent with an appropriate set of timing parameters to drive the stimulus.
    configure_agent_timing_cfg();

    // Print test configuration
    `uvm_info(`gfn, $sformatf("Test vseq properties:\n%s", this.sprint()), UVM_MEDIUM)
    print_i2c_timing_cfg(i2c_idx);

    // Wait for TXFIFO to be pre-populated with any data for READ transfers.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Data written to fifo");

    // Drive the i2c_agent to create the test stimulus.
    drive_i2c_agent_stimulus(byte_count);
  endtask


  virtual function void configure_agent_timing_cfg();

    // tSetupBit need to be non-zero to detect the data bits. This represents
    // the delay through the synchronizers.
    int tSetupBit = 2;

    // Nullify the CDC instrumentation delays on the input synchronizers,
    // since SDA never truly changes simultaneously with SCL. Their happening
    // on the same cycle in simulation is due to time/cycle quantization.
    // Drive SDA a cycle early to account for CDC delays, if CDC is enabled.
    // Hold SDA a cycle longer to account for CDC delays, if CDC is enabled.
    if (cfg.en_dv_cdc) begin
      tSetupBit++;
      cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldBit = 1;
    end
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupBit = tSetupBit;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockLow = half_period_cycles - tSetupBit;

    // tClockPulse needs to be "slightly" longer than the clock period.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockPulse = half_period_cycles;

    // tHoldStart and tClockStart need to be non-zero to make the start condition detectable.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldStart = half_period_cycles;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockStart = half_period_cycles;

    // tClockStop, tSetupStop, and tHoldStop have to be non-zero to make the stop condition
    // detectable.
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockStop = tSetupBit;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupStop = half_period_cycles;
    cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldStop = half_period_cycles;

  endfunction : configure_agent_timing_cfg


  // Drive the i2c_agent to create test stimulus, which in this case is the following:
  // - Drive a READ transfer
  // - Drive a WRITE transfer, writing the same data collected by the READ transfer
  //
  virtual task drive_i2c_agent_stimulus(input int size);

    // Drive a READ-transfer with the Agent-Controller
    begin
      i2c_transaction txn;
      i2c_target_base_seq m_i2c_host_seq;

      // Create the single read transfer
      begin
        i2c_item xfer;
        `uvm_create_obj(i2c_item, xfer)
        xfer.addr = choose_address ? (i2c_device_address_0 | (r & ~i2c_device_mask_0)) :
                                     (i2c_device_address_1 | (r & ~i2c_device_mask_1));
        xfer.addr_ack = i2c_pkg::ACK;
        xfer.dir = i2c_pkg::READ;
        xfer.bus_op = BusOpRead;
        xfer.num_data = size;
        for (int j = 0; j < size; j++) begin
          // By default, everything should be ACK'd except for the final byte of any read transfer
          i2c_pkg::acknack_e acknack = (j == (size - 1)) ? i2c_pkg::NACK :
                                                           i2c_pkg::ACK;
          xfer.data_ack_q.push_back(acknack);
          xfer.data_q.push_back('0); // It's a read operation, so this data is just a placeholder.
        end
        xfer.start = 1;
        xfer.stop = 1;

        txn.push_back(xfer);
      end

      // Convert the transfer into a suitable form for the agent to drive. Then drive it.
      `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
      convert_i2c_txn_to_drv_q(txn, m_i2c_host_seq.req_q);
      m_i2c_host_seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]);
    end

    `uvm_info(`gfn, $sformatf("cfg.m_i2c_agent_cfgs[i2c_idx].rcvd_rd_byte = %0d",
      cfg.m_i2c_agent_cfgs[i2c_idx].rcvd_rd_byte), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("size = %0d", size), UVM_MEDIUM)
    // Check the above read-transfer has completed.
    `DV_CHECK(cfg.m_i2c_agent_cfgs[i2c_idx].rcvd_rd_byte == size)
    `DV_CHECK(p_sequencer.i2c_rd_fifos[i2c_idx].used() == 1,
      "Exactly one READ-transfer item should have been captured!")
    `uvm_info(`gfn, "Read transfer complete.", UVM_MEDIUM)

    // Take the read-data from the previous transfer, then create a WRITE-transfer which
    // returns the same data to the DUT.
    begin
      i2c_transaction txn;
      i2c_target_base_seq m_i2c_host_seq;

      // The i2c_agent monitor's analysis port is connected up to a TLM fifo 'i2c_rd_fifos' in the
      // chip_env vseqr. Pull the item from this fifo to get the previously read data, and use it to
      // populate the new write transfer.
      begin
        i2c_item xfer;
        `DV_CHECK(p_sequencer.i2c_rd_fifos[i2c_idx].try_get(xfer))

        // We can re-use the data fields of the READ transfer item to create the WRITE transfer.
        // Since no one else will be using this item, just modify in place and reuse it.
        xfer.addr = choose_address ? (i2c_device_address_0 | (r & ~i2c_device_mask_0)) :
                                     (i2c_device_address_1 | (r & ~i2c_device_mask_1));
        xfer.addr_ack = i2c_pkg::ACK;
        xfer.dir = i2c_pkg::WRITE;
        xfer.bus_op = BusOpWrite;
        // For a WRITE transfer, all data bytes should be ACK'd.
        xfer.data_ack_q.delete();
        repeat (xfer.num_data) xfer.data_ack_q.push_back(i2c_pkg::ACK);
        xfer.start = 1;
        xfer.stop = 1;

        txn.push_back(xfer);
      end

      `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
      convert_i2c_txn_to_drv_q(txn, m_i2c_host_seq.req_q);
      m_i2c_host_seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]);
    end

  endtask : drive_i2c_agent_stimulus


  // This function is duplicated from the block level i2c_base_vseq
  // TODO(#23920) Find a unified home for this logic, which will probably be inside the i2c agent.
  //
  virtual function void convert_i2c_txn_to_drv_q(i2c_transaction txn, ref i2c_item drv_q[$]);

    // Loop over each transfer, determine what to drive based on the control flags
    foreach (txn[transfer_i]) begin
      i2c_item xfer = txn[transfer_i];

      // The transfer must begin with a 'START' or 'RSTART' condition
      if (xfer.start) begin
        // 'START' condition begins the transfer (and transaction)
        i2c_item start_txn;
        `uvm_create_obj(i2c_item, start_txn)
        start_txn.drv_type = HostStart;
        drv_q.push_back(start_txn);
      end else if (xfer.rstart_front) begin
        // 'RSTART' condition begins the transfer (which is only possible if the previous
        // transfer ends with an RSTART).
        // Sending duplicate messages with .drv_type = HostRStart would cause the driver to
        // produce invalid traffic, so simply omit sending it here.
        `uvm_info(`gfn, "Omitting .drv_type = HostRStart item from driver queue.", UVM_FULL)
      end else begin
        `uvm_fatal(`gfn, "Can't create a transfer that doesn't start with either START or RSTART!")
      end

      // Add the address+direction byte
      begin
        i2c_item addr_txn;
        `uvm_create_obj(i2c_item, addr_txn)
        addr_txn.drv_type = HostData;
        addr_txn.wdata[7:1] = xfer.addr[6:0];
        addr_txn.wdata[0] = xfer.dir;
        drv_q.push_back(addr_txn);
      end

      // Add items for all the data bytes
      foreach (xfer.data_q[i]) begin
        case (xfer.bus_op)
          BusOpWrite: begin
            // For write bytes, we drive the data using 'HostData'
            i2c_item data_txn;
            `uvm_create_obj(i2c_item, data_txn)
            data_txn.drv_type = HostData;
            data_txn.wdata = xfer.data_q[i];
            drv_q.push_back(data_txn);
          end
          BusOpRead: begin
            // For read bytes, we wait 8 bit-periods then ack or nack (The driver behaviour
            // for both 'HostAck' and 'HostNAck' include this 8-bit wait)
            i2c_item acknack_txn;
            `uvm_create_obj(i2c_item, acknack_txn)
            acknack_txn.drv_type = (xfer.data_ack_q[i] == i2c_pkg::ACK) ? HostAck : HostNAck;
            drv_q.push_back(acknack_txn);
          end
          default:;
        endcase
      end

      // Add the 'STOP' or 'RSTART' condition to end the transfer
      if (xfer.stop) begin
        // 'STOP' condition ends the transfer (and transaction)
        i2c_item stop_txn;
        `uvm_create_obj(i2c_item, stop_txn)
        stop_txn.drv_type = HostStop;
        drv_q.push_back(stop_txn);
      end else if (xfer.rstart_back) begin
        // 'RSTART' condition ends the transfer
        i2c_item rstart_txn;
        `uvm_create_obj(i2c_item, rstart_txn)
        rstart_txn.drv_type = HostRStart;
        drv_q.push_back(rstart_txn);
      end else begin
        `uvm_fatal(`gfn, "Can't create a transfer that doesn't end with either STOP or RSTART!")
      end
    end

  endfunction : convert_i2c_txn_to_drv_q


endclass : chip_sw_i2c_device_tx_rx_vseq
