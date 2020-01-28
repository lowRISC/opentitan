// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_base_vseq extends cip_base_vseq #(
    .CFG_T               (i2c_env_cfg),
    .RAL_T               (i2c_reg_block),
    .COV_T               (i2c_env_cov),
    .VIRTUAL_SEQUENCER_T (i2c_virtual_sequencer)
  );
  `uvm_object_utils(i2c_base_vseq)

  i2c_request_e  i2c_request = i2c_rw;

  // enable interrupts
  rand bit [NumI2cIntr-1:0] en_intr;

  // random delays to access fifo/intr, may be controlled in extended seq
  rand uint dly_to_access_fifo;

  // various knobs to enable certain routines
  bit do_interrupt      = 1'b1;

  constraint dly_to_access_fifo_c {
    dly_to_access_fifo inside {[1:100]};
  }

  `uvm_object_new

  virtual task body();
    // override cip_base_vseq.body()
  endtask : body

  virtual task dut_shutdown();
    // check for pending i2c operations and wait for them to complete
    super.dut_shutdown();

    // wait for fmt and rx operations to complete
    `uvm_info(`gfn, "waiting for idle", UVM_HIGH)
    //cfg.m_i2c_agent_cfg.vif.wait_for_idle();
    `uvm_info(`gfn, "Simulation done", UVM_HIGH)
  endtask

  // setup basic i2c features
  virtual task i2c_host_init();
    `uvm_info(`gfn, "initialize i2c host registers", UVM_HIGH)

    // configure i2c_agent
    cfg.m_i2c_agent_cfg.max_dly_to_send_ack     = 5;
    cfg.m_i2c_agent_cfg.max_dly_to_send_nack    = 5;
    cfg.m_i2c_agent_cfg.max_dly_to_send_stop    = 5;
    cfg.m_i2c_agent_cfg.max_dly_to_send_rd_data = 5;

    // progrem ctrl reg
    ral.ctrl.enablehost.set(1'b1);
    csr_update(ral.ctrl);

    // program ovrd reg
    ral.ovrd.txovrden.set(1'b0);
    // allow randomize sclval and sdaval since txovrden is unset
    ral.ovrd.sclval.set($urandom_range(1,0));
    ral.ovrd.sdaval.set($urandom_range(1,0));
    csr_update(ral.ovrd);

    if (do_interrupt) begin
      // program intr_enable reg
      ral.intr_enable.set(en_intr);
      csr_update(ral.intr_enable);

      // program timeout_ctrl reg
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.timeout_ctrl.val, value inside {[10 : 100]};)
      `DV_CHECK_RANDOMIZE_FATAL(ral.timeout_ctrl.en)
      csr_update(ral.timeout_ctrl);

      // program fifo_ctrl reg
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.fifo_ctrl.rxilvl, value <= 4;)
      `DV_CHECK_RANDOMIZE_FATAL(ral.fifo_ctrl.fmtilvl)
      csr_update(ral.fifo_ctrl);
    end
    `uvm_info(`gfn, "host init is done", UVM_HIGH)
  endtask : i2c_host_init

  virtual task i2c_host_read();
    //`uvm_info(`gfn, "host starts doing read", UVM_HIGH)
  endtask: i2c_host_read

  virtual task i2c_host_write();
    //`uvm_info(`gfn, "host starts doing write", UVM_HIGH)
  endtask: i2c_host_write

  // control i2c_agent monitor
  virtual task i2c_monitor_ctrl(bit enb_mon);
    cfg.m_i2c_agent_cfg.en_tx_monitor = enb_mon;
    cfg.m_i2c_agent_cfg.en_rx_monitor = enb_mon;
    if (enb_mon)
      `uvm_info(`gfn, $sformatf("i2c monitor is enable, enb_mon=%b", enb_mon), UVM_LOW)
    else
      `uvm_info(`gfn, $sformatf("i2c monitor is disable, enb_mon=%b", enb_mon), UVM_LOW)
  endtask : i2c_monitor_ctrl

  // customized version for i2c host by overriding one defined in cip_base_vseq class
  virtual task clear_all_interrupts();
    bit [TL_DW-1:0] data;
    foreach (intr_state_csrs[i]) begin
      csr_rd(.ptr(intr_state_csrs[i]), .value(data));
      `uvm_info(`gfn, $sformatf("%s 0x%08h", intr_state_csrs[i].get_name(), data), UVM_LOW)
      if (data != 0) begin
        `uvm_info(`gtn, $sformatf("Clearing %0s", intr_state_csrs[i].get_name()), UVM_LOW)
        csr_wr(.csr(intr_state_csrs[i]), .value(data));
        csr_rd(.ptr(intr_state_csrs[i]), .value(data));
        `uvm_info(`gfn, $sformatf("intr_state_csrs 0x%08h", data), UVM_LOW)
        // unlike other IP, fmt_watermark is initially triggered due to
        // FMT fifo depth is low at reset
        `DV_CHECK_EQ(data, 1)
      end
    end
    `DV_CHECK_EQ(cfg.intr_vif.sample(), {NUM_MAX_INTERRUPTS{1'b0}})
  endtask : clear_all_interrupts

  // task to wait for fmt fifo not full
  virtual task wait_for_fmt_fifo_not_full();
    bit [TL_DW-1:0] status;

    if (ral.ctrl.enablehost.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      csr_spinwait(.ptr(ral.status.fmtfull), .exp_data(1'b0),
                   .spinwait_delay_ns(dly_to_access_fifo));
    end
    `uvm_info(`gfn, "wait_for_tx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_fmt_fifo_not_full

  // task to wait for rx fifo not full, will be overriden in overflow test
  virtual task wait_for_rx_fifo_not_full();
    if (ral.ctrl.enablehost.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      csr_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b0),
                   .spinwait_delay_ns(dly_to_access_fifo),
                   .timeout_ns(50_000_000)); // use longer timeout as i2c freq is low
    end
    `uvm_info(`gfn, "wait_for_rx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_rx_fifo_not_full

  // in some corner cases, we can't drive when the uart item is almost done
  // wait for this period to pass
  virtual task wait_when_in_ignored_period(bit tx = 0, bit rx = 0);
    wait (!(
        (tx && cfg.m_i2c_agent_cfg.vif.clk_i inside `TX_IGNORED_PERIOD) ||
        (rx && cfg.m_i2c_agent_cfg.vif.clk_i inside `RX_IGNORED_PERIOD)
      ));
    `uvm_info(`gfn, "wait_when_in_ignored_period is done", UVM_HIGH)
  endtask : wait_when_in_ignored_period
  
endclass : i2c_base_vseq
