// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
typedef class i2c_scoreboard;

class i2c_env_cfg extends cip_base_env_cfg #(.RAL_T(i2c_reg_block));

  i2c_scoreboard scoreboard;
  virtual i2c_dv_if i2c_dv_vif;

  ////////////////////////////////
  // Test Configuration Options //
  ////////////////////////////////

  rand i2c_agent_cfg m_i2c_agent_cfg;
  i2c_seq_cfg seq_cfg;

  i2c_target_addr_mode_e target_addr_mode = Addr7BitMode; // (dv supports 7-bit addresses only)

  int        spinwait_timeout_ns = 10_000_000; // 10ms
  int        long_spinwait_timeout_ns = 400_000_000;

  // Constrain the direction of each randomly-generated Agent-Controller transfer.
  // - These values become weights in a randcase statement, so setting to 0 will disable a
  //   particular direction of transfer.
  int        wr_pct = 1;
  int        rd_pct = 1;
  // If enabled, 'bad_addr_pct' gives each generated Agent-Controller transaction the possibilty
  // of selecting an address that does not match the DUT's configuration.
  int        bad_addr_pct = 0;

  // Constrain the min/max number of bytes that should make up a stimulated
  // DUT-target transaction. Note this constrains each whole transaction, and RSTARTs
  // may be injected to break it up into many smaller contiguous transfers.
  int        min_data = 1;
  int        max_data = 60;
  // RSTART injection rate percentage (1-100)
  int        rs_pct = 10;

  // This sets the minimum length of a transfer (START/RSTART -> RSTART/STOP) within
  // any larger transaction. A transfer with no data, where the address byte is NACK'd,
  // is possible with our stimulus approach, and this can break checking in certain
  // circumstances.
  int        min_xfer_len = 0;

  // The vseq stimulus has routines to generate interrupt and polling-driven stimulus.
  // This bit (settable via a plusarg) allows individual tests to specify which generic
  // handling routines should be used. (0==polling/1==interrupts)
  bit        use_intr_handler = 1'b0;

  // If set, 50% chance to enable ACK Control Mode
  bit        ack_ctrl_en = 1'b0;

  // Enabling these bits add extra delays to the testbench processes that read back the ACQFIFO and
  // write into the TXFIFO for DUT-Target operation. This allows stimulating full/empty stalls and
  // stretches.
  bit        slow_acq = 1'b0;
  bit        slow_txq = 1'b0;

  // In Target-mode, read data is created by i2c_base_seq::fetch_txn().
  // Random TXFIFO flush events make it difficult to check read path integrity.
  // By setting 'read_rnd_data = 1', the expected read data is instead collected
  // right at the input of TXFIFO. On TXFIFO reset, any expected read data is
  // also flushed.
  bit        read_rnd_data = 0;

  ////////////////////////////////
  // Helper Variables (not cfg) //
  ////////////////////////////////

  int        sent_acq_cnt;
  int        rcvd_acq_cnt;
  bit [7:0]  lastbyte;

  // Flags for the 'ack_stop' test
  int        sent_ack_stop = 0;
  int        rcvd_ack_stop = 0;

  // Flags that test sequences can use to cleanup
  bit        stop_intr_handler = 1'b0;
  bit        read_all_acq_entries = 1'b0;

  uint scl_frequency = 100; //in KHz

  `uvm_object_utils_begin(i2c_env_cfg)
    `uvm_field_object(m_i2c_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = i2c_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    m_i2c_agent_cfg = i2c_agent_cfg::type_id::create("m_i2c_agent_cfg");
    m_i2c_agent_cfg.if_mode = Device;
    m_i2c_agent_cfg.ok_to_end_delay_ns = 5000;
    m_i2c_agent_cfg.target_addr_mode = Addr7BitMode;
    m_tl_agent_cfg.max_outstanding_req = 1;

    seq_cfg = i2c_seq_cfg::type_id::create("seq_cfg");

    // set num_interrupts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

  // this function is called after reset or end of vseq run
  virtual function void reset_seq_cfg();
    seq_cfg.en_rx_overflow      = 1'b0;
    seq_cfg.en_rx_threshold     = 1'b0;
    seq_cfg.en_sda_unstable     = 1'b0;
    seq_cfg.en_scl_interference = 1'b0;
    seq_cfg.en_sda_interference = 1'b0;

    // target mode cfg params.
    slow_acq = 0;
    wr_pct = 1;
    rd_pct = 1;
    min_data = 1;
    max_data = 60;
    read_all_acq_entries = 0;
    sent_ack_stop = 0;
    rcvd_ack_stop = 0;
  endfunction : reset_seq_cfg

  task wait_fifo_not_empty(i2c_analysis_fifo fifo);
    while (!fifo.is_empty()) begin
      clk_rst_vif.wait_clks(1);
    end
  endtask

endclass : i2c_env_cfg
