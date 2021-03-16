// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_base_vseq extends cip_base_vseq #(.CFG_T               (uart_env_cfg),
                                             .RAL_T               (uart_reg_block),
                                             .COV_T               (uart_env_cov),
                                             .VIRTUAL_SEQUENCER_T (uart_virtual_sequencer));
  `uvm_object_utils(uart_base_vseq)

  // variables for dut initialization
  rand baud_rate_e baud_rate; // set baud rate
  rand bit en_tx;             // enable tx
  rand bit en_rx;             // enable rx
  rand bit en_parity;         // enable parity
  rand bit odd_parity;        // enable odd parity
  rand bit en_noise_filter;   // enable noise filter

  // glitch control
  rand uint uart_period_glitch_pct;

  // enable interrupts
  rand bit [NumUartIntr-1:0] en_intr;

  // random delays to access fifo/intr, may be controlled in extended seq
  rand uint dly_to_access_fifo;

  // various knobs to enable certain routines
  bit do_interrupt      = 1'b1;

  constraint uart_period_glitch_pct_c {
    uart_period_glitch_pct inside {[0:10]};
  }

  constraint baud_rate_c {
    // when the uart frequency is very close to core freq, disable noise filter and glitch,
    // otherwise, not enough timing margin to predict status correctly in scb
    if (baud_rate == BaudRate1p5Mbps && p_sequencer.cfg.clk_freq_mhz == ClkFreq24Mhz) {
      en_noise_filter == 0;
      uart_period_glitch_pct == 0;
    }
    // constrain nco not over nco.get_n_bits
    `CALC_NCO(baud_rate, p_sequencer.cfg.ral.ctrl.nco.get_n_bits(),
        p_sequencer.cfg.clk_freq_mhz) < 2 ** p_sequencer.cfg.ral.ctrl.nco.get_n_bits();
  }

  constraint dly_to_access_fifo_c {
    // uart clk is slow, up to 2 ** 16 (65_536) slower than pclk
    // 1_000_000 is about 1.5 * 65_536
    dly_to_access_fifo dist {
      0                   :/ 1,
      [1      :100]       :/ 1,
      [101    :10_000]    :/ 8,
      [10_001 :1_000_000] :/ 1
    };
  }

  `uvm_object_new

  virtual task dut_shutdown();
    super.dut_shutdown();
    // wait for tx and rx operations to complete
    `uvm_info(`gfn, "waiting for idle", UVM_HIGH)
    cfg.m_uart_agent_cfg.vif.wait_for_idle();
    `uvm_info(`gfn, "done waiting for idle", UVM_HIGH)
  endtask

  // setup basic uart features
  virtual task uart_init();
    int nco = get_nco(baud_rate, cfg.clk_freq_mhz, ral.ctrl.nco.get_n_bits());

    // we skip writting some CSRs at the last 1-2 uart cycles, when baud rate is 1.5Mbps, uart
    // cycle is small, need to reduce the TL delay, so that the write doesn't happen at the
    // ignore period
    if (baud_rate == BaudRate1p5Mbps && p_sequencer.cfg.clk_freq_mhz == ClkFreq24Mhz) begin
      if (cfg.m_tl_agent_cfg.d_ready_delay_max > 5) cfg.m_tl_agent_cfg.d_ready_delay_max = 5;
    end

    cfg.m_uart_agent_cfg.set_uart_period_glitch_pct(uart_period_glitch_pct);

    // cfg uart agent to set the baud rate & parity
    cfg.m_uart_agent_cfg.set_baud_rate(baud_rate);
    cfg.m_uart_agent_cfg.set_parity(en_parity, odd_parity);
    ral.ctrl.tx.set(en_tx);
    ral.ctrl.rx.set(en_rx);
    ral.ctrl.nf.set(en_noise_filter);
    ral.ctrl.parity_en.set(en_parity);
    ral.ctrl.parity_odd.set(odd_parity);
    if (do_interrupt) `DV_CHECK_RANDOMIZE_FATAL(ral.ctrl.rxblvl)
    ral.ctrl.nco.set(nco);
    csr_update(ral.ctrl);

    if (do_interrupt) begin
      ral.intr_enable.set(en_intr);
      csr_update(ral.intr_enable);

      // from spec - timeout value may be reduced by 1.5 clock periods at some corner cases
      // need >= char time + 2, so that receiving next character can reset the counter
      // before timer is expired
      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.timeout_ctrl.val,
                                     value inside {[10 + en_parity + 2 : 100]};)
      `DV_CHECK_RANDOMIZE_FATAL(ral.timeout_ctrl.en)
      csr_update(ral.timeout_ctrl);

      `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.fifo_ctrl.rxilvl,
                                     value <= 4;)
      `DV_CHECK_RANDOMIZE_FATAL(ral.fifo_ctrl.txilvl)
      csr_update(ral.fifo_ctrl);
    end
  endtask

  // clear fifos
  virtual task clear_fifos(bit clear_tx_fifo, bit clear_rx_fifo);
    ral.fifo_ctrl.rxrst.set(clear_rx_fifo);
    ral.fifo_ctrl.txrst.set(clear_tx_fifo);
    csr_update(ral.fifo_ctrl);
  endtask

  // set uart parity for the dut and the agent
  virtual task set_parity(bit en_parity, bit odd_parity);
    // cfg uart dut
    ral.ctrl.parity_en.set(en_parity);
    ral.ctrl.parity_odd.set(odd_parity);
    csr_update(ral.ctrl);
    // cfg uart agent
    cfg.m_uart_agent_cfg.set_parity(en_parity, odd_parity);
  endtask

  // set uart baud rate for the dut and the agent
  virtual task set_baud_rate(baud_rate_e baud_rate);
    int nco = get_nco(baud_rate, cfg.clk_freq_mhz, ral.ctrl.nco.get_n_bits());
    ral.ctrl.nco.set(nco);
    csr_update(ral.ctrl);
    // cfg uart agent
    cfg.m_uart_agent_cfg.set_baud_rate(baud_rate);
  endtask

  virtual task spinwait_txidle();
    if (ral.ctrl.tx.get_mirrored_value()) begin
      // use a very big timeout as it takes long time to flush all the items
      csr_spinwait(.ptr(ral.status.txidle), .exp_data(1'b1), .timeout_ns(40_000_000),
                   .spinwait_delay_ns($urandom_range(0, 1000)));
    end
  endtask

  virtual task spinwait_rxidle();
    if (ral.ctrl.rx.get_mirrored_value()) begin
      csr_spinwait(.ptr(ral.status.rxidle), .exp_data(1'b1),
                   .spinwait_delay_ns($urandom_range(0, 1000)));
    end
  endtask

  // task to send a byte of data out of dut
  virtual task send_tx_byte(byte data);
    csr_wr(.ptr(ral.wdata), .value(data));
  endtask

  // task to send a byte of data into dut, can override it to test error cases
  virtual task send_rx_byte(byte data);
    drive_rx_error_byte(.parity_err(0), .frame_err(0), .data(data));
  endtask

  // drive rx byte with parity_err or frame_err, data is random
  virtual task drive_rx_error_byte(bit parity_err, bit frame_err, byte data = $urandom);
    uart_seq send_rx_seq;
    `uvm_create_on(send_rx_seq, p_sequencer.uart_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(send_rx_seq,
                                   data == local::data;
                                   parity_err == local::parity_err;
                                   frame_err  == local::frame_err;
                                   )
    `uvm_send(send_rx_seq)
  endtask : drive_rx_error_byte

  // task to check if byte received is what was sent by the agent
  virtual task chk_rx_byte(logic [7:0] exp_data);
    bit [TL_DW-1:0] rdata;
    csr_rd(.ptr(ral.rdata), .value(rdata));
    // do check but only if rx is enabled
    if (ral.ctrl.rx.get_mirrored_value()) begin
      if (!cfg.under_reset) `DV_CHECK_EQ(rdata, exp_data)
    end
  endtask

  // task to read all the rx bytes
  virtual task read_all_rx_bytes();
    bit [TL_DW-1:0] rdata, fifo_status;

    csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
    repeat (get_field_val(ral.fifo_status.rxlvl, fifo_status))  begin
      wait_ignored_period_and_read_rdata(rdata);
    end

    csr_rd(.ptr(ral.fifo_status), .value(fifo_status));

    `uvm_info(`gfn, "read_all_rx_bytes is done", UVM_HIGH)
  endtask : read_all_rx_bytes

  // override this function to control RX fifo level
  virtual task rand_read_rx_byte(uint weight_to_skip);
    bit [TL_DW-1:0] rdata, fifo_status;
    int             rxlvl;

    randcase
      1: begin // read & check one byte
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
        if(rxlvl > 0) begin
          wait_ignored_period_and_read_rdata(rdata);
        end
      end
      1: begin // read & check some bytes
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        rxlvl = get_field_val(ral.fifo_status.rxlvl, fifo_status);
        if(rxlvl > 0) begin
          repeat ($urandom_range(1, rxlvl)) wait_ignored_period_and_read_rdata(rdata);
        end
      end
      1: begin // read & check all rx bytes
        read_all_rx_bytes();
      end
      weight_to_skip: begin
      end
    endcase
  endtask : rand_read_rx_byte

  // read rx data from CSR rdata, but wait until it's not in igored period
  virtual task wait_ignored_period_and_read_rdata(ref bit [TL_DW-1:0] rdata);
    wait_when_in_ignored_period(.rx(1));
    csr_rd(.ptr(ral.rdata), .value(rdata));
  endtask

  // task to wait for all rx bytes to be sent
  virtual task wait_for_all_tx_bytes();
    bit [TL_DW-1:0] fifo_status, status;

    if (ral.ctrl.tx.get_mirrored_value()) begin
      do begin
        if (cfg.under_reset) break;
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
        cfg.clk_rst_vif.wait_clks(dly_to_access_fifo);
        csr_rd(.ptr(ral.fifo_status), .value(fifo_status));
        csr_rd(.ptr(ral.status),      .value(status));
      end while (get_field_val(ral.fifo_status.txlvl, fifo_status) > 0 ||
                 get_field_val(ral.status.txidle, status) == 0);
    end

    `uvm_info(`gfn, "wait_for_all_tx_bytes is done", UVM_HIGH)
  endtask : wait_for_all_tx_bytes

  // task to wait for tx fifo not full
  virtual task wait_for_tx_fifo_not_full();
    bit [TL_DW-1:0] status;

    if (ral.ctrl.tx.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0),
                   .spinwait_delay_ns(dly_to_access_fifo));
    end

    `uvm_info(`gfn, "wait_for_tx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_tx_fifo_not_full

  // task to wait for rx fifo not full, will be overriden in overflow test
  virtual task wait_for_rx_fifo_not_full();
    if (ral.ctrl.rx.get_mirrored_value()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
      csr_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b0),
                   .spinwait_delay_ns(dly_to_access_fifo),
                   .timeout_ns(50_000_000)); // use longer timeout as uart freq is low
    end
    `uvm_info(`gfn, "wait_for_rx_fifo_not_full is done", UVM_HIGH)
  endtask : wait_for_rx_fifo_not_full

  // in some corner cases, we can't drive when the uart item is almost done
  // wait for this period to pass
  virtual task wait_when_in_ignored_period(bit tx = 0, bit rx = 0);
    wait (!(
        (tx && cfg.m_uart_agent_cfg.vif.uart_tx_clk_pulses inside `TX_IGNORED_PERIOD) ||
        (rx && cfg.m_uart_agent_cfg.vif.uart_rx_clk_pulses inside `RX_IGNORED_PERIOD)
      ));
    `uvm_info(`gfn, "wait_when_in_ignored_period is done", UVM_HIGH)
  endtask : wait_when_in_ignored_period

endclass : uart_base_vseq
