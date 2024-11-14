// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// simply trigger each interrupt one by one and check interrupt pin & reg in the seq
class uart_intr_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_intr_vseq)

  constraint num_trans_c {
    num_trans inside {[1:4]};
  }

  // Make interrupts easy to predict and fast to simulate - lower the freq so that there is enough
  // time to read status and check but enforce a minimum frequency when performing many runs in a
  // test to keep runtime reasonable.
  constraint baud_rate_extra_c {
    baud_rate <= BaudRate230400;
    num_trans > 2 -> baud_rate >= BaudRate115200;
  }

  `uvm_object_new

  task body();
    uart_intr_e uart_intr;
    // will inject parity/stop error in this case
    cfg.m_uart_agent_cfg.en_rx_checks = 0;
    for (int i = 1; i <= num_trans; i++) begin
      if (cfg.stop_transaction_generators()) break;
      `DV_CHECK_RANDOMIZE_FATAL(this)
      uart_init();

      repeat (NumUartIntr) begin
        if (cfg.stop_transaction_generators()) break;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(uart_intr,
                                           uart_intr != NumUartIntr;)
        `uvm_info(`gfn, $sformatf("\nTesting %0s", uart_intr.name), UVM_LOW)
        drive_and_check_one_intr(uart_intr);

        // quickly clear all intr & fifo, make sure no leftover for next iteration
        clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(1));
        // tx may have unfinished transaction
        spinwait_txidle();
        dut_shutdown();
        csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));
      end
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
    end
  endtask : body

  task drive_and_check_one_intr(uart_intr_e uart_intr);
    int tx_fifo_max_size;
    uint bit_num_per_trans;

    // 1 start + 8 data + 1 parity (if enabled) + 1 stop
    bit_num_per_trans = 10 + cfg.m_uart_agent_cfg.en_parity;

    case (uart_intr)
      TxWatermark: begin
        int level = ral.fifo_ctrl.txilvl.get_mirrored_value();
        int watermark_bytes = get_tx_watermark_bytes_by_level(level);
        if (!en_tx) return;
        // First byte is immediately popped from TX FIFO (for transmission) and watermark based upon
        // TX FIFO level excluding in-transmission byte. Add 1 to watermark_bytes here to give the
        // number of bytes required to move over the watermark threshold.
        watermark_bytes += 1;
        drive_tx_bytes(.num_bytes(watermark_bytes - 1));
        if (level == 0) begin
          // Need a brief delay while the data byte is popped and the interrupt returns high
          cfg.clk_rst_vif.wait_clks(1);
        end
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        drive_tx_bytes(.num_bytes(1));
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        // wait until it drops below watermark
        csr_spinwait(.ptr(ral.fifo_status.txlvl),
                     .exp_data(get_tx_watermark_bytes_by_level(level)),
                     .compare_op(CompareOpLt));
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
        // interrupt should remain asserted whilst FIFO level is below watermark, writes to
        // intr_state to clear have no effect
        csr_wr(.ptr(ral.intr_state), .value(1 << uart_intr));
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        drive_tx_bytes(.num_bytes(watermark_bytes + 1));
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end

      TxEmpty: begin
        if (!en_tx) return;
        // Interrupt should begin high, before we push anything to the TX FIFO
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        // Write a single byte to the TX FIFO which will immediately begin transmission
        drive_tx_bytes(.num_bytes(1));
        // Need a brief delay while the data byte is popped and the interrupt returns high
        cfg.clk_rst_vif.wait_clks(1);
        // Interrupt should now be high as TX FIFO will be empty (but TX of first byte on-going)
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        // Drive a second byte
        drive_tx_bytes(.num_bytes(1));
        // Interrupt should now be low as second byte will be in TX FIFO whilst TX of first byte is
        // ongoing
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        // wait until TX FIFO empties again
        csr_spinwait(.ptr(ral.fifo_status.txlvl),
                     .exp_data(0),
                     .compare_op(CompareOpEq));
        // Interrupt should now be high
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
        // interrupt should remain asserted whilst FIFO is empty, writes to intr_state to clear have
        // no effect
        csr_wr(.ptr(ral.intr_state), .value(1 << uart_intr));
        check_one_intr(.uart_intr(uart_intr), .exp(1));
        // check interrupt clears when FIFO is non-empty again (2 bytes needed as first will be
        // popped for transmission).
        drive_tx_bytes(.num_bytes(2));
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end

      RxWatermark: begin
        int level = ral.fifo_ctrl.rxilvl.get_mirrored_value();
        int watermark_bytes = get_rx_watermark_bytes_by_level(level);
        drive_rx_bytes(.num_bytes(watermark_bytes - 1));
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        drive_rx_bytes(.num_bytes(1));
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx));
        // interrupt should remain asserted whilst FIFO level is above watermark, writes to
        // intr_state to clear have no effect
        csr_wr(.ptr(ral.intr_state), .value(1 << uart_intr));
        drive_rx_bytes(.num_bytes(1));
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx));
      end

      TxDone: begin
        if (en_tx) begin
          // when tx is enabled, one extra item is in the data path, total is TxFifoDepth + 1
          drive_tx_bytes(.num_bytes($urandom_range(1, TxFifoDepth + 1)));
          check_one_intr(.uart_intr(uart_intr), .exp(0));
          spinwait_txidle();
          check_one_intr(.uart_intr(uart_intr), .exp(1));
          // check interrupt is non-sticky
          csr_wr(.ptr(ral.intr_state), .value(1 << uart_intr));
          check_one_intr(.uart_intr(uart_intr), .exp(0));
        end
      end

      RxOverflow: begin
        drive_rx_bytes(.num_bytes(RxFifoDepth));
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        drive_rx_bytes(.num_bytes(1));
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx));
      end

      RxFrameErr: begin
        drive_rx_error_byte(.parity_err(0), .frame_err(1));
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx));
        sync_up_rx_from_frame_err(bit_num_per_trans);
      end

      // Follow this table from spec to verify RxBreakErr
      // Line low(bit-times)  Frame Err?  Break?     Comment
      //    <10                If STOP=0    No       Normal operation
      //  10 (with parity)       No         No       Normal zero data with STOP=1
      //  10 (no parity)         Yes        No       Frame error since STOP=0
      //  11 - RXBLVL*char       Yes        No       Break less than detect level
      //  >RXBLVL*char           Yes       Once      Frame signalled at every char-times,
      //                                             break at RXBLVL char-times
      RxBreakErr: begin
        bit [NumUartIntr-1:0] exp_intr_state;
        bit [NumUartIntr-1:0] exp_intr_state_mask = '1;
        int level = ral.ctrl.rxblvl.get_mirrored_value();
        int break_bytes = get_break_bytes_by_level(level);

        // drive one good rx char to reset DUT break cnt (allzero_cnt)
        drive_rx_bytes(.num_bytes(1));
        // clear rx fifo and interrupts triggered by above driving
        clear_fifos(.clear_tx_fifo(0), .clear_rx_fifo(1));
        csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));

        // Don't attempt to predict Tx/Rx watermark when testing RxBreakErr so we don't need to
        // predict TX/RX FIFO levels for this test.
        exp_intr_state_mask[TxWatermark] = 1'b0;
        exp_intr_state_mask[TxEmpty] = 1'b0;
        exp_intr_state_mask[RxWatermark] = 1'b0;

        fork
          begin
             drive_rx_all_0s();
          end
          begin
            // < 10 cycles 0s, expect no interrupt
            wait_for_baud_clock_cycles(9);
            // check interrupt reg & pin but not affect timing of driving uart RX
            nonblocking_check_all_intr(.exp(0), .do_clear(0), .exp_mask(exp_intr_state_mask));
            // 10th cycle
            wait_for_baud_clock_cycles(1);
            exp_intr_state[RxFrameErr]  = ~en_parity & en_rx;
            nonblocking_check_all_intr(.exp(exp_intr_state), .do_clear(0),
                .exp_mask(exp_intr_state_mask));
            // 11th cycle
            wait_for_baud_clock_cycles(1);
            exp_intr_state[RxParityErr] = en_parity & en_rx & `GET_PARITY(0, odd_parity);
            exp_intr_state[RxFrameErr]  = en_rx;
            nonblocking_check_all_intr(.exp(exp_intr_state), .do_clear(1),
                .exp_mask(exp_intr_state_mask));
          end
        join

        // disable parity & frame err check in scb, as mon can't handle line breaking
        // check them in seq
        cfg.disable_scb_rx_parity_check = 1;
        cfg.disable_scb_rx_frame_check  = 1;

        // from 11 to RXBLVL * char - 1
        if (break_bytes > 2) begin // avoid negetive value
          wait_for_baud_clock_cycles(bit_num_per_trans * (break_bytes - 1) - 11);
          nonblocking_check_all_intr(.exp(exp_intr_state), .do_clear(1),
              .exp_mask(exp_intr_state_mask));
        end
        // RXBLVL * char
        wait_for_baud_clock_cycles(bit_num_per_trans);
        exp_intr_state[RxBreakErr] = en_rx;
        nonblocking_check_all_intr(.exp(exp_intr_state), .do_clear(1),
            .exp_mask(exp_intr_state_mask));

        // RXBLVL * char * 2
        wait_for_baud_clock_cycles(bit_num_per_trans * break_bytes);
        // check break intr doesn't occur again
        exp_intr_state[RxBreakErr] = 0;
        nonblocking_check_all_intr(.exp(exp_intr_state), .exp_mask(exp_intr_state_mask));

        sync_up_rx_from_frame_err(bit_num_per_trans);
        cfg.disable_scb_rx_parity_check = 0;
        cfg.disable_scb_rx_frame_check  = 0;
      end

      RxTimeout: begin
        bit [TL_DW-1:0] rdata;
        realtime timeout_last_reset;
        uint num_bytes   = $urandom_range(1, RxFifoDepth);
        uint timeout_val = ral.timeout_ctrl.val.get_mirrored_value();
        bit  en_timeout  = ral.timeout_ctrl.en.get_mirrored_value();
        drive_rx_bytes(num_bytes);
        // wait for timeout_val-1 cycles, timeout shouldn't occur
        // wait for one more cycle, timeout occurs
        // timeout event will repeat if SW only clears the interrupt but not read the fifo
        wait_for_baud_clock_cycles(timeout_val - 1);
        check_one_intr(.uart_intr(uart_intr), .exp(0));
        wait_for_baud_clock_cycles(2);
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx & en_timeout));
        csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));
        // expect timeout again since no fifo activity
        wait_for_baud_clock_cycles(timeout_val + 1);
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx & en_timeout));
        csr_wr(.ptr(ral.intr_state), .value((1 << NumUartIntr) - 1));

        if (!en_rx) return;
        // reset timeout timer by issuing a rdata read
        timeout_last_reset = $realtime;
        csr_rd(.ptr(ral.rdata),  .value(rdata));

        // Wait until the device is about to timeout (timeout_val-2 cycles) and then
        // read or drive uart RX items to reset timeout count. More FIFO reads than FIFO writes.
        // Repeat until FIFO is empty. Timeout should never occur.
        // Delay relative to last timeout reset so subsequent CSR reads do not affect total delay.
        // Timeout value can increment in a fraction of the expected one baud-clock cycle with
        // unlucky FIFO read or RX start timing, and both can happen between timeout resets
        // (hence the need for timeout_val-2 rather than timeout_val-1).
        forever begin
          bit rxempty;
          bit rxfull;
          randcase
            5: begin // read one or more RX items (fifo read)
              csr_rd(.ptr(ral.status.rxempty), .value(rxempty));
              if (rxempty) break; // exit forever
              // use -2 to have higher tolerance to avoid timeout
              wait_until_baud_clock_cycles_after(timeout_val - 2, timeout_last_reset);
              // Read more than one byte most of the time to reduce max runtime
              repeat ($urandom_range(RxFifoDepth >> 2, 1)) begin
                timeout_last_reset = $realtime;
                csr_rd(.ptr(ral.rdata), .value(rdata));
                csr_rd(.ptr(ral.status.rxempty), .value(rxempty));
                if (rxempty) break; // exit repeat
              end
            end
            1: begin // drive one RX item (fifo write)
              // use -2 to have higher tolerance to avoid timeout
              int cycles = timeout_val - bit_num_per_trans - 2;
              wait_until_baud_clock_cycles_after(cycles > 0 ? cycles : 0, timeout_last_reset);
              csr_rd(.ptr(ral.status.rxfull), .value(rxfull));
              // it won't reset timeout timer if receiving a rx item when fifo is full
              if (rxfull) begin
                timeout_last_reset = $realtime; // timeout resets upon FIFO read request
                csr_rd(.ptr(ral.rdata), .value(rdata));
              end else begin
                drive_rx_bytes(.num_bytes(1));
                timeout_last_reset = $realtime; // timeout resets upon finishing receiving RX byte
              end
            end
          endcase
          check_one_intr(.uart_intr(uart_intr), .exp(0));
        end

        // no rx timeout if no data in rx fifo
        wait_for_baud_clock_cycles(timeout_val * 2);
        check_one_intr(.uart_intr(uart_intr), .exp(0));
      end

      RxParityErr: begin
        drive_rx_error_byte(.parity_err(1), .frame_err(0));
        check_one_intr(.uart_intr(uart_intr), .exp(en_rx & en_parity));
      end
    endcase
  endtask : drive_and_check_one_intr

  // only check one interrupt state and pin
  task check_one_intr(uart_intr_e uart_intr, bit exp);
    bit [TL_DW-1:0] act_intr_state;
    bit exp_pin;

    // Check pins first in case they change during register read
    exp_pin = exp & en_intr[uart_intr];
    if (!cfg.under_reset) `DV_CHECK_EQ(cfg.intr_vif.pins[uart_intr], exp_pin, $sformatf(
        "uart_intr name/val: %0s/%0d, en_intr: %0h", uart_intr.name, uart_intr, en_intr))
    csr_rd(.ptr(ral.intr_state), .value(act_intr_state));
    if (!cfg.under_reset) `DV_CHECK_EQ(act_intr_state[uart_intr], exp)
  endtask : check_one_intr

  // check all interrupt state and pin
  task check_all_intr(bit [NumUartIntr-1:0] exp, bit do_clear = 0,
      bit [NumUartIntr-1:0] exp_mask = '1);
    bit [NumUartIntr-1:0] act_intr_state;
    bit [NumUartIntr-1:0] exp_pin;

    // Check pins first in case they change during register read
    exp_pin = exp & en_intr;
    if (!cfg.under_reset) `DV_CHECK_EQ(cfg.intr_vif.pins[NumUartIntr-1:0] & exp_mask, exp_pin,
        $sformatf("uart_intr val: %0h, en_intr: %0h", exp, en_intr))
    csr_rd(.ptr(ral.intr_state), .value(act_intr_state));
    if (!cfg.under_reset) `DV_CHECK_EQ(act_intr_state & exp_mask, exp)

    if (do_clear) begin
      csr_wr(.ptr(ral.intr_state), .value(exp));
    end
  endtask : check_all_intr

  task nonblocking_check_all_intr(bit [NumUartIntr-1:0] exp, bit do_clear = 0,
      bit [NumUartIntr-1:0] exp_mask = '1);
    fork
        check_all_intr(exp, do_clear, exp_mask);
    join_none
  endtask : nonblocking_check_all_intr

  // drive all 0s to verify break error
  task drive_rx_all_0s();
    uart_seq send_rx_seq;
    `uvm_create_on(send_rx_seq, p_sequencer.uart_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(send_rx_seq,
                                   data       == 0;
                                   parity     == 0;
                                   frame_err  == 1;
                                   )
    `uvm_send(send_rx_seq)
  endtask

  // drive all 1s for sync up with design after frame error
  task sync_up_rx_from_frame_err(uint cycles_per_trans);
    cfg.m_uart_agent_cfg.vif.uart_rx = 1;
    wait_for_baud_clock_cycles(cycles_per_trans);
  endtask

  task wait_until_baud_clock_cycles_after(uint cycles, realtime start);
    realtime elapsed = $realtime - start;
    realtime delay = (cfg.m_uart_agent_cfg.vif.uart_clk_period * cycles);
    if (delay <= elapsed) return;
    #(delay - elapsed);
  endtask

  task wait_for_baud_clock_cycles(uint cycles);
    #(cfg.m_uart_agent_cfg.vif.uart_clk_period * cycles);
  endtask

  task drive_tx_bytes(int num_bytes);
    repeat (num_bytes) begin
      byte tx_byte;
      `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
      send_tx_byte(.data(tx_byte));
    end
    // wait for 1 cycle to allow interrupt triggered
    cfg.clk_rst_vif.wait_clks(1);
  endtask : drive_tx_bytes

  task drive_rx_bytes(int num_bytes);
    repeat (num_bytes) begin
      byte rx_byte;
      `DV_CHECK_STD_RANDOMIZE_FATAL(rx_byte)
      send_rx_byte(.data(rx_byte));
    end
  endtask : drive_rx_bytes

endclass : uart_intr_vseq
