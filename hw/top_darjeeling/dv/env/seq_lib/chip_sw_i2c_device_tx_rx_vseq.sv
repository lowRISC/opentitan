// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// By default this test will use a randomly selected instance i2c_idx.
// To make a dedicated test for instance i, where i is in {0,1,2}, the test
// should run with an option:
//     run_opts: ["+i2c_idx=i"]

class chip_sw_i2c_device_tx_rx_vseq extends chip_sw_i2c_tx_rx_vseq;
  import i2c_pkg::*;

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

  constraint i2c_idx_c {
    i2c_idx inside {[0 : NUM_I2CS-1]};
  }

  constraint i2c_byte_count_c {
    byte_count inside {[30 : 60]};
  }

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
    drive_i2c_agent_stimulus();
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

  // Convert the transfer into a suitable form for the agent to drive. Then drive it.
  local task convert_and_drive_xfer(i2c_transaction txn);
    i2c_target_base_seq i2c_host_seq = i2c_target_base_seq::type_id::create("i2c_host_seq");
    convert_i2c_txn_to_drv_q(txn, i2c_host_seq.req_q);
    i2c_host_seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]);
  endtask

  // Fill in the I2C transfer before driving it
  local function void fill_i2c_xfer_flds(i2c_item item, rw_e dir, bus_op_e bus_op);
    item.addr = choose_address ? (i2c_device_address_0 | (r & ~i2c_device_mask_0)) :
                                 (i2c_device_address_1 | (r & ~i2c_device_mask_1));
    item.addr_ack = ACK;
    item.num_data = byte_count;
    item.bus_op   = bus_op;
    item.dir      = dir;
    item.start    = 1;
    item.stop     = 1;

    // For BusOpWrite, the job for N/Acking the bytes is on the I2C device.
    if (bus_op == BusOpRead) begin
      for (int j = 0; j < byte_count; j++) begin
        // By default, everything should be ACK'd except for the final byte to terminate the
        // transfer.
        acknack_e acknack = (j == (byte_count - 1)) ? NACK : ACK;
        item.data_ack_q.push_back(acknack);
      end
    end
  endfunction

  local task create_and_drive_i2c_xfer(i2c_item item, rw_e dir, bus_op_e bus_op);
    i2c_transaction txn;

    fill_i2c_xfer_flds(item, dir, bus_op);
    txn.push_back(item);
    convert_and_drive_xfer(txn);
  endtask

  // Drive the i2c_agent to create test stimulus, which in this case is the following:
  // - Drive a READ transfer
  // - Drive a WRITE transfer, writing the same data collected by the READ transfer
  virtual task drive_i2c_agent_stimulus();
    // Create the single read transfer
    i2c_item xfer = i2c_item::type_id::create("xfer");

    create_and_drive_i2c_xfer(xfer, READ, BusOpRead);

    // Check if the agent has received all the data bytes contained in the TX FIFO of device.
    if (cfg.m_i2c_agent_cfgs[i2c_idx].rcvd_rd_byte != byte_count) begin
      `uvm_fatal(`gfn,
                 $sformatf("Agent received %0d / %0d bytes",
                           cfg.m_i2c_agent_cfgs[i2c_idx].rcvd_rd_byte,
                           byte_count))
    end

    // Check if the i2c_monitor has pushed the transfer item contains the information of the read.
    if (!p_sequencer.i2c_rd_fifos[i2c_idx].used())
      `uvm_fatal(`gfn, "Analysis FIFO is not yet filled with the transferred item")

    `uvm_info(`gfn, "Read transfer completed.", UVM_MEDIUM)

    // De-allocate and emptied the storage of the i2c_item and i2c_transaction queue for the next
    // write transfer.
    xfer = null;

    // Take the read bytes from the previous transfer, then create a WRITE-transfer that write
    // those bytes to the device.
    //
    // The i2c_agent monitor's analysis port is connected up to a TLM fifo 'i2c_rd_fifos' in the
    // chip_env vseqr. Pull the item from this fifo to get the previously read data, and use it to
    // populate the new write transfer.
    `DV_CHECK(p_sequencer.i2c_rd_fifos[i2c_idx].try_get(xfer))

    // The read bytes are pushed into data_q by the i2c_monitor. data_ack_q still contains the N/Ack
    // information from the previous read transfer but that shouldn't matter for this Vseq as
    // N/Acking is a device's job entirely in a write transfer.
    create_and_drive_i2c_xfer(xfer, WRITE, BusOpWrite);
  endtask : drive_i2c_agent_stimulus

endclass : chip_sw_i2c_device_tx_rx_vseq
