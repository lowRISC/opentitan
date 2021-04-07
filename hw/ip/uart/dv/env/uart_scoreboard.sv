// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_scoreboard extends cip_base_scoreboard #(.CFG_T(uart_env_cfg),
                                                    .RAL_T(uart_reg_block),
                                                    .COV_T(uart_env_cov));
  `uvm_component_utils(uart_scoreboard)

  virtual uart_if uart_vif;

  // local variables
  local bit tx_enabled;
  local bit rx_enabled;
  local int uart_tx_clk_pulses;
  local int uart_rx_clk_pulses;

  // expected values
  local bit tx_full_exp, rx_full_exp, tx_empty_exp, rx_empty_exp, tx_idle_exp, rx_idle_exp;
  local int txlvl_exp, rxlvl_exp;
  local bit [NumUartIntr-1:0] intr_exp;
  local bit [7:0] rdata_exp;
  // store tx/rx_q at TL address phase
  local int tx_q_size_at_addr_phase, rx_q_size_at_addr_phase;
  local bit [NumUartIntr-1:0] intr_exp_at_addr_phase;

  // non sticky interrupts are edge-triggered
  // set it when interrupt is triggered, clear it when interrupt condition is no longer true
  local bit tx_watermark_triggered = 1;
  local bit rx_watermark_triggered = 0;

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(uart_item)    uart_tx_fifo;
  uvm_tlm_analysis_fifo #(uart_item)    uart_rx_fifo;

  // local queues to hold incoming packets pending comparison
  uart_item tx_q[$];
  // when item is removed from fifo and being sent on UART tx interface, store it in this queue
  uart_item tx_processing_item_q[$];
  uart_item rx_q[$];

  // it takes 3 cycles to move item from fifo to process, which delays reg status change
  // and it also takes 3 cycles to trigger tx matermark interrupt
  parameter uint NUM_CLK_DLY_TO_UPDATE_TX_WATERMARK = 3;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uart_tx_fifo = new("uart_tx_fifo", this);
    uart_rx_fifo = new("uart_rx_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    uart_vif = cfg.m_uart_agent_cfg.vif;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_uart_tx_fifo();
      process_uart_rx_fifo();
    join_none
  endtask

  virtual task process_uart_tx_fifo();
    uart_item act_item, exp_item;
    forever begin
      uart_tx_fifo.get(act_item);

      `uvm_info(`gfn, $sformatf("received uart tx item:\n%0s", act_item.sprint()), UVM_HIGH)
      `DV_CHECK_EQ(tx_processing_item_q.size(), 1)
      exp_item = tx_processing_item_q.pop_front();
      // move item from fifo to process
      if (tx_q.size > 0) begin
        tx_processing_item_q.push_back(tx_q.pop_front());
        `uvm_info(`gfn, $sformatf("After drop one item, new tx_q size: %0d", tx_q.size), UVM_HIGH)
      end
      compare(act_item, exp_item, "TX");
      // after an item is sent, check to see if size dipped below watermark
      predict_tx_watermark_intr();

      if (tx_q.size() == 0 && tx_processing_item_q.size() == 0) begin
        intr_exp[TxEmpty] = 1;
      end
    end
  endtask

  virtual task process_uart_rx_fifo();
    uart_item item;
    forever begin
      uart_rx_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received uart rx item:\n%0s", item.sprint()), UVM_HIGH)

      if (rx_enabled) begin
        bit parity = `GET_PARITY(item.data, ral.ctrl.parity_odd.get_mirrored_value());
        bit parity_err = ral.ctrl.parity_en.get_mirrored_value() && parity != item.parity;

        if (parity_err) begin
          intr_exp[RxParityErr] = 1;
          `uvm_info(`gfn, $sformatf("dropped uart rx item due to partiy err:\n%0s",
                                    item.sprint()), UVM_HIGH)
        end
        if (!item.stop_bit) begin
          intr_exp[RxFrameErr] = 1;
          `uvm_info(`gfn, $sformatf("dropped uart rx item due to frame err:\n%0s",
                                    item.sprint()), UVM_HIGH)
        end
        if (!parity_err && item.stop_bit == 1) begin // no parity/frame error
          if (rx_q.size < UART_FIFO_DEPTH) begin
            rx_q.push_back(item);
            predict_rx_watermark_intr();
          end
          else begin
            intr_exp[RxOverflow] = 1;
            `uvm_info(`gfn, $sformatf("dropped uart rx item due to overflow:\n%0s",
                                      item.sprint()), UVM_HIGH)
          end
        end // no parity/frame error
      end // if (rx_enabled)
    end // forever
  endtask

  // when interrupt is non-sticky, interrupt will be triggered once unless it exits interrupt
  // condition
  virtual function bit get_non_sticky_interrupt(bit cur_intr, bit new_intr, ref bit triggered);
    bit final_intr = cur_intr || (new_intr & ~triggered);
    if (!new_intr)       triggered = 0;
    else if (final_intr) triggered = 1;

    return final_intr;
  endfunction

  virtual function void predict_tx_watermark_intr(uint tx_q_size = tx_q.size);
    uint watermark = get_watermark_bytes_by_level(ral.fifo_ctrl.txilvl.get_mirrored_value(),
                                                  UartTx);
    intr_exp[TxWatermark] = get_non_sticky_interrupt(.cur_intr(intr_exp[TxWatermark]),
                                                     .new_intr(tx_q_size < watermark),
                                                     .triggered(tx_watermark_triggered));
  endfunction

  virtual function void predict_rx_watermark_intr(uint rx_q_size = rx_q.size);
    uint watermark = get_watermark_bytes_by_level(ral.fifo_ctrl.rxilvl.get_mirrored_value(),
                                                  UartRx);
    intr_exp[RxWatermark] = get_non_sticky_interrupt(
        .cur_intr(intr_exp[RxWatermark]),
        .new_intr(rx_q_size >= watermark && rx_enabled),
        .triggered(rx_watermark_triggered));
  endfunction

  // we don't model uart cycle-acurrately, ignore checking when item is just/almost finished
  function bit is_in_ignored_period(uart_dir_e dir);
    case (dir)
      UartTx: return uart_tx_clk_pulses inside `TX_IGNORED_PERIOD;
      UartRx: return uart_rx_clk_pulses inside `RX_IGNORED_PERIOD;
    endcase
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end

      // need to store uart_tx/tx_clk_pulses earlier to predict reg value correctly
      uart_tx_clk_pulses   = uart_vif.uart_tx_clk_pulses;
      uart_rx_clk_pulses   = uart_vif.uart_rx_clk_pulses;
      // save fifo level at address phase
      tx_q_size_at_addr_phase = tx_q.size;
      rx_q_size_at_addr_phase = rx_q.size;
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      "ctrl": begin
        if (write && channel == AddrChannel) begin
          if (cfg.en_cov) begin
            cov.baud_rate_w_core_clk_cg.sample(cfg.m_uart_agent_cfg.baud_rate, cfg.clk_freq_mhz);
          end

          tx_enabled = ral.ctrl.tx.get_mirrored_value();
          rx_enabled = ral.ctrl.rx.get_mirrored_value();

          if ((tx_q.size > 0 || tx_processing_item_q.size > 0) && tx_enabled) begin
            if (tx_q.size > 0 && tx_processing_item_q.size == 0) begin
              tx_processing_item_q.push_back(tx_q.pop_front());
              fork begin
                int loc_tx_q_size = tx_q.size();
                cfg.clk_rst_vif.wait_n_clks(NUM_CLK_DLY_TO_UPDATE_TX_WATERMARK);
                predict_tx_watermark_intr(loc_tx_q_size);
              end join_none
            end
          end
        end
      end
      "wdata": begin
        // if tx is enabled, push exp tx data to q
        if (write && channel == AddrChannel) begin
          uart_item tx_item = uart_item::type_id::create("tx_item");

          tx_item.data = item.a_data;
          if (tx_q.size() < UART_FIFO_DEPTH) begin
            tx_q.push_back(tx_item);
            `uvm_info(`gfn, $sformatf("After push one item, tx_q size: %0d", tx_q.size), UVM_HIGH)
          end else begin
            `uvm_info(`gfn, $sformatf(
                "Drop tx item: %0h, tx_q size: %0d, uart_tx_clk_pulses: %0d",
                csr.get_mirrored_value(), tx_q.size(), uart_tx_clk_pulses), UVM_MEDIUM)
          end
          fork begin
            int loc_tx_q_size = tx_q.size();
            // remove 1 when it's abort to be popped for transfer
            if (tx_enabled && tx_processing_item_q.size == 0 && tx_q.size > 0) loc_tx_q_size--;
            // use negedge to avoid race condition
            cfg.clk_rst_vif.wait_n_clks(NUM_CLK_DLY_TO_UPDATE_TX_WATERMARK);
            if (ral.ctrl.slpbk.get_mirrored_value()) begin
              // if sys loopback is on, tx item isn't sent to uart pin but rx fifo
              uart_item tx_item = tx_q.pop_front();
              if (rx_enabled && (rx_q.size < UART_FIFO_DEPTH)) begin
                rx_q.push_back(tx_item);
                predict_rx_watermark_intr();
              end
            end else if (tx_enabled && tx_processing_item_q.size == 0 && tx_q.size > 0) begin
              tx_processing_item_q.push_back(tx_q.pop_front());
            end
            predict_tx_watermark_intr(loc_tx_q_size);
          end join_none
        end // write && channel == AddrChannel
      end
      "fifo_ctrl": begin
        if (write && channel == AddrChannel) begin
          // these fields are WO
          bit txrst_val = bit'(get_field_val(ral.fifo_ctrl.txrst, item.a_data));
          bit rxrst_val = bit'(get_field_val(ral.fifo_ctrl.rxrst, item.a_data));
          if (txrst_val) begin
            if (tx_enabled && tx_q.size > 0 && tx_processing_item_q.size == 0) begin
              // keep the 1st item in the queue, as it's being sent
              tx_processing_item_q.push_back(tx_q.pop_front());
            end
            tx_q.delete();
            void'(ral.fifo_ctrl.txrst.predict(.value(0), .kind(UVM_PREDICT_WRITE)));
            if (cfg.en_cov) begin
              cov.fifo_level_cg.sample(.dir(UartTx),
                                       .lvl(ral.fifo_status.txlvl.get_mirrored_value()),
                                       .rst(1));
            end
          end
          if (rxrst_val) begin
            rx_q.delete();
            void'(ral.fifo_ctrl.rxrst.predict(.value(0), .kind(UVM_PREDICT_WRITE)));
            if (cfg.en_cov) begin
              cov.fifo_level_cg.sample(.dir(UartRx),
                                       .lvl(ral.fifo_status.rxlvl.get_mirrored_value()),
                                       .rst(1));
            end
          end
          // recalculate watermark when RXILVL/TXILVL is updated
          predict_rx_watermark_intr();
          fork begin
            int loc_tx_q_size = tx_q.size();
            if (txrst_val) cfg.clk_rst_vif.wait_n_clks(NUM_CLK_DLY_TO_UPDATE_TX_WATERMARK);
            predict_tx_watermark_intr(loc_tx_q_size);
          end join_none
        end // write && channel == AddrChannel
      end
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          intr_exp |= item.a_data;
          if (cfg.en_cov) begin
            foreach (intr_exp[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
        end
      end
      "status": begin
        if (!write) begin // read
          case (channel)
            AddrChannel: begin // predict at address phase
              tx_full_exp  = tx_q.size >= UART_FIFO_DEPTH;
              tx_empty_exp = tx_q.size == 0;
              tx_idle_exp  = tx_q.size == 0 && tx_processing_item_q.size == 0;
              rx_full_exp  = rx_q.size == UART_FIFO_DEPTH;
              rx_empty_exp = rx_q.size == 0;
              rx_idle_exp  = (uart_rx_clk_pulses == 0) || !rx_enabled;
            end
            DataChannel: begin // check at data phase
              int uart_bits;

              do_read_check = 1'b0;
              // don't check it in system loopback mode. Since no pin activity, hard to predict
              // status value, check it in seq
              if (ral.ctrl.slpbk.get_mirrored_value()) return;

              uart_bits  = 10 + ral.ctrl.parity_en.get_mirrored_value();

              // ignore corner case when item is about to complete, also fifo is changing from
              // full to not full and it's at ignored period
              if (!(tx_enabled && tx_q_size_at_addr_phase == UART_FIFO_DEPTH
                    && is_in_ignored_period(UartTx))) begin
                `DV_CHECK_EQ(get_field_val(ral.status.txfull, item.d_data), tx_full_exp, $sformatf(
                    "check tx_full fail: tx_en = %0d, tx_q.size = %0d, uart_tx_clk_pulses = %0d",
                    tx_enabled, tx_q_size_at_addr_phase, uart_tx_clk_pulses))
              end
              if (!(rx_enabled && is_in_ignored_period(UartRx) &&
                    rx_q_size_at_addr_phase inside {UART_FIFO_DEPTH - 1, UART_FIFO_DEPTH})) begin
                `DV_CHECK_EQ(get_field_val(ral.status.rxfull, item.d_data), rx_full_exp, $sformatf(
                    "check rx_full fail: rx_en = %0d, rx_q.size = %0d, uart_rx_clk_pulses = %0d",
                    rx_enabled, rx_q_size_at_addr_phase, uart_rx_clk_pulses))
              end

              // when tx_q.size = 1 and it's at last 2 cycles, can't predict if txempty is set
              if (!(tx_enabled && tx_q_size_at_addr_phase inside {0, 1}
                    && is_in_ignored_period(UartTx))) begin
                `DV_CHECK_EQ(get_field_val(ral.status.txempty, item.d_data), tx_empty_exp,
                    $sformatf("check tx_empty fail: uart_tx_clk_pulses = %0d, tx_q.size = %0d",
                              uart_tx_clk_pulses, tx_q_size_at_addr_phase))
              end
              if (!(rx_q_size_at_addr_phase inside {0, 1} && is_in_ignored_period(UartRx))) begin
                `DV_CHECK_EQ(get_field_val(ral.status.rxempty, item.d_data), rx_empty_exp,
                    $sformatf("check rx_empty fail: uart_rx_clk_pulses = %0d, rx_q.size = %0d",
                              uart_rx_clk_pulses, rx_q_size_at_addr_phase))
              end

              // don't check when it's last item at last 2 cycles
              if (!(tx_q_size_at_addr_phase == 0 && is_in_ignored_period(UartTx))) begin
                `DV_CHECK_EQ(get_field_val(ral.status.txidle, item.d_data), tx_idle_exp, $sformatf(
                    "check tx_idle fail: tx_en = %0d, tx_q.size = %0d, uart_tx_clk_pulses = %0d",
                    tx_enabled, tx_q_size_at_addr_phase, uart_tx_clk_pulses))
              end
              // rx_idle_exp will be clear/set during START/STOP bit,
              // but we don't use exactly same clk as DUT
              // check rx_idle==1 when uart_rx_clk_pulses>0, rx_idle==0 when uart_rx_clk_pulses==0
              // ignore checking when uart_rx_clk_pulses==1 or uart_rx_clk_pulses==uart_bits
              if (!(uart_rx_clk_pulses inside {1, uart_bits}) || !rx_enabled) begin
                `DV_CHECK_EQ(get_field_val(ral.status.rxidle, item.d_data), rx_idle_exp, $sformatf(
                    "check rx_idle fail: rx_en = %0d, uart_rx_clk_pulses = %0d",
                    rx_enabled, uart_rx_clk_pulses))
              end
            end
          endcase
        end // if (!write)
      end // status
      "intr_state": begin
        if (write && channel == AddrChannel) begin // write & address phase
          bit[TL_DW-1:0] intr_wdata = item.a_data;
          fork begin
            bit [NumUartIntr-1:0] pre_intr = intr_exp;
            // add 1 cycle delay to avoid race condition when fifo changing and interrupt clearing
            // occur simultaneously
            cfg.clk_rst_vif.wait_clks(1);
            intr_exp &= ~intr_wdata;
          end join_none
        end else if (!write && channel == AddrChannel) begin // read & addr phase
          intr_exp_at_addr_phase = intr_exp;
        end else if (!write && channel == DataChannel) begin // read & data phase
          uart_intr_e     intr;
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          do_read_check = 1'b0;
          foreach (intr_exp[i]) begin
            intr = uart_intr_e'(i); // cast to enum to get interrupt name
            if (cfg.en_cov) begin
              cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
            end
            // don't check it when it's in ignored period
            if (intr inside {TxWatermark, TxEmpty}) begin // TX interrupts
              if (is_in_ignored_period(UartTx)) continue;
            end else begin // RX interrupts
              // RxTimeout, RxBreakErr is checked in seq
              if (intr inside {RxTimeout, RxBreakErr} || is_in_ignored_period(UartRx) ||
                  (cfg.disable_scb_rx_parity_check && intr == RxParityErr) ||
                  (cfg.disable_scb_rx_frame_check  && intr == RxFrameErr)
                  ) begin
                continue;
              end
            end
            `DV_CHECK_EQ(item.d_data[i], intr_exp_at_addr_phase[i],
                         $sformatf("Interrupt: %0s", intr.name));
            `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & intr_exp[i]),
                         $sformatf("Interrupt_pin: %0s", intr.name));
          end
        end // read & data phase
      end
      "rdata": begin
        if (!write) begin // read only
          // rdata is removed from fifo after addr phase
          if (channel == AddrChannel) begin
            if (rx_q.size() > 0) begin
              uart_item rx_q_item = rx_q.pop_front();
              rdata_exp = rx_q_item.data;
              predict_rx_watermark_intr();
            end else begin
              do_read_check = 1'b0;
              `uvm_error(`gfn, "unexpected read when fifo is empty")
            end // rx_q.size() == 0
          end else begin //DataChannel
            void'(csr.predict(.value(rdata_exp), .kind(UVM_PREDICT_READ)));
          end // channel == DataChannel
        end // !write
      end
      "fifo_status": begin
        if (!write) begin
          case (channel)
            AddrChannel: begin // predict at address phase
              txlvl_exp = tx_q.size() > UART_FIFO_DEPTH ? UART_FIFO_DEPTH : tx_q.size();
              rxlvl_exp = rx_q.size();
            end
            DataChannel: begin // check at data phase
              bit [5:0] txlvl_act, rxlvl_act;

              void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
              txlvl_act = ral.fifo_status.txlvl.get_mirrored_value();
              rxlvl_act = ral.fifo_status.rxlvl.get_mirrored_value();

              if (txlvl_act == txlvl_exp) begin
                // match, do nothing
              end else if (tx_enabled && is_in_ignored_period(UartTx) &&
                           absolute(txlvl_act - txlvl_exp) == 1) begin
                // allow +/-1 difference as txlvl is reduced when previous item is in stop phase
                // match, do nothing
              end else begin
                `uvm_error(`gfn, $sformatf("txlvl mismatch exp: %0d (+/-1), act: %0d,\
                                 clk_pulses: %0d", txlvl_exp, txlvl_act, uart_tx_clk_pulses))
              end

              if (rxlvl_act == rxlvl_exp) begin
                // match, do nothing
              end else if (rx_enabled && is_in_ignored_period(UartRx)
                           && absolute(rxlvl_act - rxlvl_exp) == 1) begin
                // allow +/-1 difference as rxlvl is reduced when previous item is in stop phase
                // match, do nothing
              end else begin
                `uvm_error(`gfn, $sformatf("rxlvl mismatch exp: %0d (+/-1), act: %0d,\
                                 clk_pulses: %0d", rxlvl_exp, rxlvl_act, uart_rx_clk_pulses))
              end
              do_read_check = 1'b0;

              if (cfg.en_cov) begin
                cov.fifo_level_cg.sample(.dir(UartTx), .lvl(txlvl_act), .rst(0));
                cov.fifo_level_cg.sample(.dir(UartRx), .lvl(rxlvl_act), .rst(0));
              end
            end
          endcase
        end
      end
      "val": begin
        if (!write && channel == DataChannel) begin
          // rx oversampled val, check in test
          do_read_check = 1'b0;
        end
      end
      "ovrd", "intr_enable", "timeout_ctrl": begin
        // no speical handle is needed
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  function void compare(uart_item act, uart_item exp, string dir = "TX");
    if (!act.compare(exp)) begin
      `uvm_error(`gfn, $sformatf("%s item mismatch!\nexp:\n%0s\nobs:\n%0s",
                                  dir, exp.sprint(), act.sprint()))
    end
    else begin
      `uvm_info(`gfn, $sformatf("%s item match!\nexp:\n%0s\nobs:\n%0s",
                                 dir, exp.sprint(), act.sprint()), UVM_HIGH)
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset the ral model and local fifos and queues
    uart_tx_fifo.flush();
    uart_rx_fifo.flush();
    tx_q.delete();
    tx_processing_item_q.delete();
    rx_q.delete();
    // reset local variables
    uart_tx_clk_pulses   = 0;
    uart_rx_clk_pulses   = 0;
    tx_q_size_at_addr_phase = 0;
    rx_q_size_at_addr_phase = 0;
    tx_watermark_triggered  = 1;
    rx_watermark_triggered  = 0;
    tx_enabled           = ral.ctrl.tx.get_reset();
    rx_enabled           = ral.ctrl.rx.get_reset();
    tx_full_exp          = ral.status.txfull.get_reset();
    rx_full_exp          = ral.status.rxfull.get_reset();
    tx_empty_exp         = ral.status.txempty.get_reset();
    rx_empty_exp         = ral.status.rxempty.get_reset();
    tx_idle_exp          = ral.status.txidle.get_reset();
    rx_idle_exp          = ral.status.rxidle.get_reset();
    txlvl_exp            = ral.fifo_status.txlvl.get_reset();
    rxlvl_exp            = ral.fifo_status.rxlvl.get_reset();
    intr_exp             = ral.intr_state.get_reset();
    rdata_exp            = ral.rdata.get_reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(uart_item, uart_tx_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(uart_item, uart_rx_fifo)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, tx_q)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, tx_processing_item_q)
    `DV_EOT_PRINT_Q_CONTENTS(uart_item, rx_q)
  endfunction

endclass
