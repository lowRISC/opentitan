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

  // enable interrupts
  rand bit [NumI2cIntr-1:0] en_intr;

  // random delays to access fifo/intr, may be controlled in extended seq
  rand uint dly_to_access_fifo;

  // various knobs to enable certain routines
  bit do_interrupt  = 1'b1;

  constraint dly_to_access_fifo_c {
    dly_to_access_fifo inside {[1:100]};
  }

  constraint en_intr_c {
    en_intr inside {[0: ((1 << NumI2cIntr) - 1)]};
  }

  `uvm_object_new

  virtual task dut_shutdown();
    // check for pending i2c operations and wait for them to complete
    super.dut_shutdown();
    // wait for fmt and rx operations to complete
    `uvm_info(`gfn, "waiting for idle", UVM_DEBUG)
    //cfg.m_i2c_agent_cfg.vif.wait_for_idle();
    `uvm_info(`gfn, "simulation done", UVM_DEBUG)
  endtask

  // setup basic i2c features
  virtual task initialize_host();
    `uvm_info(`gfn, "initialize i2c host registers", UVM_DEBUG)

    // configure i2c_agent_cfg
    cfg.m_i2c_agent_cfg.max_delay_ack  = 5;
    cfg.m_i2c_agent_cfg.max_delay_nack = 5;
    cfg.m_i2c_agent_cfg.max_delay_stop = 5;
    cfg.m_i2c_agent_cfg.max_delay_data = 5;
    // program ctrl reg
    ral.ctrl.enablehost.set(I2C_FLAG_ON);
    csr_update(ral.ctrl);
    // disable override the logic level of output pins
    ral.ovrd.txovrden.set(I2C_FLAG_OFF);
    csr_update(ral.ovrd);
    // reset fmt_fifo and rx_fifo
    ral.fifo_ctrl.rxrst.set(I2C_FLAG_ON);
    ral.fifo_ctrl.fmtrst.set(I2C_FLAG_ON);
    csr_update(ral.fifo_ctrl);

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
  endtask : initialize_host

  // program timing registers
  virtual task program_timing_regs(bit [TL_DW-1:0] val[]);
    // program timing register
    csr_wr(.csr(ral.timing0), .value(val[0]));
    csr_wr(.csr(ral.timing1), .value(val[1]));
    csr_wr(.csr(ral.timing2), .value(val[2]));
    csr_wr(.csr(ral.timing3), .value(val[3]));
    csr_wr(.csr(ral.timing4), .value(val[4]));
  endtask : program_timing_regs

  // customized version for i2c host by overriding one defined in cip_base_vseq class
  virtual task clear_all_interrupts();
    bit [TL_DW-1:0] data;
    foreach (intr_state_csrs[i]) begin
      csr_rd(.ptr(intr_state_csrs[i]), .value(data));
      `uvm_info(`gfn, $sformatf("%s 0x%08h", intr_state_csrs[i].get_name(), data), UVM_DEBUG)
      if (data != 0) begin
        csr_wr(.csr(intr_state_csrs[i]), .value(data));
        csr_rd(.ptr(intr_state_csrs[i]), .value(data));
        // TODO: check the initial value fmt_watermark interrupt in/out of reset
        //`DV_CHECK_EQ(data, 0)
      end
    end
    `DV_CHECK_EQ(cfg.intr_vif.sample(), {NUM_MAX_INTERRUPTS{1'b0}})
  endtask : clear_all_interrupts

  // task to wait for fmt fifo not full
  virtual task wait_for_fmt_fifo_not_full();
    bit [TL_DW-1:0] status;

    if (ral.ctrl.enablehost.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      csr_spinwait(.ptr(ral.status.fmtfull), .exp_data(I2C_FLAG_OFF),
                   .spinwait_delay_ns(dly_to_access_fifo));
    end
    `uvm_info(`gfn, "wait_for_tx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_fmt_fifo_not_full

  // task to wait for rx fifo not full, will be overriden in overflow test
  virtual task wait_for_rx_fifo_not_full();
    if (ral.ctrl.enablehost.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      csr_spinwait(.ptr(ral.status.rxfull), .exp_data(I2C_FLAG_OFF),
                   .spinwait_delay_ns(dly_to_access_fifo),
                   .timeout_ns(50_000_000)); // use longer timeout as i2c freq is low
    end
    `uvm_info(`gfn, "wait_for_rx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_rx_fifo_not_full

  // function to directly pass timing_* to i2c_agent_cfg.*
  virtual function update_agent_cfg(bit [TL_DW-1:0] val[]);
    {cfg.m_i2c_agent_cfg.tlow,    cfg.m_i2c_agent_cfg.thigh}   = val[0];
    {cfg.m_i2c_agent_cfg.t_f,     cfg.m_i2c_agent_cfg.t_r}     = val[1];
    {cfg.m_i2c_agent_cfg.thd_sta, cfg.m_i2c_agent_cfg.tsu_sta} = val[2];
    {cfg.m_i2c_agent_cfg.tsu_dat, cfg.m_i2c_agent_cfg.thd_dat} = val[3];
    {cfg.m_i2c_agent_cfg.t_buf,   cfg.m_i2c_agent_cfg.tsu_sto} = val[4];
  endfunction : update_agent_cfg

  // function to control i2c_agent monitor
  virtual function config_agent_monitor(bit enb_mon);
    cfg.m_i2c_agent_cfg.en_monitor = enb_mon;
  endfunction : config_agent_monitor

endclass : i2c_base_vseq
