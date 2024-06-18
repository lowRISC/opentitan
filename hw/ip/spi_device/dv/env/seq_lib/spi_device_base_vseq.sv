// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_base_vseq extends cip_base_vseq #(
        .CFG_T               (spi_device_env_cfg),
        .RAL_T               (spi_device_reg_block),
        .COV_T               (spi_device_env_cov),
        .VIRTUAL_SEQUENCER_T (spi_device_virtual_sequencer)
    );
  `uvm_object_utils(spi_device_base_vseq)

  // knob to control sending dummy transaction or incompleted opcode
  int allow_dummy_trans_pct = 5;

  rand bit sck_polarity;
  rand bit sck_phase;
  rand bit host_bit_dir;
  rand bit device_bit_dir;

  // core clk freq / spi clk freq is from 1/4 to 8. use below 2 var to represent the ratio
  // if spi_freq_faster,  core_spi_freq_ratio = spi clk freq / core clk freq (1:4)
  // if !spi_freq_faster, core_spi_freq_ratio = core clk freq / spi clk freq (1:8)
  rand uint core_spi_freq_ratio;
  rand bit  spi_freq_faster;

  bit kill_spi_device_flash_auto_rsp;

  // core clk freq / spi clk freq is from 1/4 to 8
  constraint freq_c {
    core_spi_freq_ratio inside {[1:8]};
    spi_freq_faster -> core_spi_freq_ratio <= 4;
  }
  //Reducing the number of transactions to avoid hitting timeout
  constraint num_trans_c {
    num_trans < 15;
  }

  `uvm_object_new

  virtual task apply_reset(string kind = "HARD");
    super.apply_reset(kind);
    cfg.do_spi_clk_configure = 1;
    cfg.do_addr_4b_cfg = 1;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.scoreboard_clear_mems();
    delay_after_reset_before_access_csr();
    void'(cfg.spi_cfg_sema.try_get());
    cfg.spi_cfg_sema.put();
  endtask : dut_init

  virtual task read_and_check_all_csrs_after_reset();
    delay_after_reset_before_access_csr();
    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task delay_after_reset_before_access_csr();
    // SPI inputs are async. It takes 2 cycles to synchronize them to status CSR
    cfg.clk_rst_vif.wait_clks(2);
  endtask

  // configure the clock frequence
  virtual task spi_clk_init();
    if (cfg.do_spi_clk_configure) begin
      cfg.spi_host_agent_cfg.csb_sel_in_cfg = 0;
      if (spi_freq_faster) begin
        cfg.spi_host_agent_cfg.sck_period_ps = cfg.clk_rst_vif.clk_period_ps / core_spi_freq_ratio;
      end else begin
        cfg.spi_host_agent_cfg.sck_period_ps = cfg.clk_rst_vif.clk_period_ps * core_spi_freq_ratio;
      end

      // min inactive time needs to be 2 core clks.
      cfg.spi_host_agent_cfg.min_idle_ns_after_csb_drop = cfg.clk_rst_vif.clk_period_ps / 1000 * 2;
      cfg.spi_host_agent_cfg.max_idle_ns_after_csb_drop = cfg.clk_rst_vif.clk_period_ps / 1000 * 10;

      cfg.do_spi_clk_configure = 0;
    end
  endtask

  virtual task spi_host_wait_on_busy();
    spi_host_flash_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
    `DV_SPINWAIT(
      while (1) begin
        cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
        `uvm_info(`gfn, "Sending READ_STATUS#1", UVM_DEBUG)
        `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                      opcode == READ_STATUS_1;
                                      address_q.size() == 0;
                                      payload_q.size() == 1;
                                      read_size == 1;)
        `uvm_send(m_spi_host_seq)
        // bit 0 is busy bit
        if (m_spi_host_seq.rsp.payload_q[0][0] === 0) break;
      end,
      "Timed out",
      default_timeout_ns * 2
    )
  endtask

  virtual task spi_device_flash_auto_rsp_nonblocking();
    spi_device_flash_seq spi_device_seq;
    `uvm_create_on(spi_device_seq, p_sequencer.spi_sequencer_d)
    spi_device_seq.is_forever_rsp_seq = 1;
    fork
      begin : isolation_thread
        fork
          wait(kill_spi_device_flash_auto_rsp);
          `uvm_send(spi_device_seq)
        join_any
        disable fork;
      end : isolation_thread
    join_none
  endtask

  task post_start();
    super.post_start();
    // kill nonblocking seq
    kill_spi_device_flash_auto_rsp = 1;
  endtask

  task pre_start();
    super.pre_start();
    `uvm_info(`gfn, $sformatf("[PRE_START] - Test will run: num_trans = %0d",num_trans), UVM_NONE)
  endtask

  // send dummy item
  virtual task spi_host_xfer_dummy_item();
    spi_host_dummy_seq m_spi_host_seq;
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                   csb_sel inside {FW_FLASH_CSB_ID, TPM_CSB_ID};)
    `uvm_send(m_spi_host_seq)
  endtask

endclass : spi_device_base_vseq
