// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_tx_rx_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_tx_rx_vseq)

  rand uint num_tx_bytes;
  rand uint num_rx_bytes;
  rand uint dly_to_next_trans;
  rand uint dly_to_access_intr;
  rand bit  wait_for_idle;
  rand uint weight_to_skip_rx_read;
  rand uint dly_to_rx_read;


  constraint num_trans_c {
    num_trans inside {[1:20]};
  }

  constraint num_tx_bytes_c {
    num_tx_bytes dist {
      1       :/ 2,
      [2:10]  :/ 5,
      [11:15] :/ 5,
      [16:20] :/ 2
    };
  }

  constraint num_rx_bytes_c {
    num_rx_bytes dist {
      1       :/ 2,
      [2:10]  :/ 5,
      [11:15] :/ 5,
      [16:20] :/ 2
    };
  }

  constraint dly_to_next_trans_c {
    dly_to_next_trans dist {
      0           :/ 5,  // more back2back transaction
      [1:100]     :/ 5,
      [100:10000] :/ 2
    };
  }

  constraint dly_to_access_intr_c {
    dly_to_access_intr dist {
      0                   :/ 1,
      [1      :100]       :/ 5,
      [101    :10_000]    :/ 3,
      [10_001 :1_000_000] :/ 1
    };
  }

  constraint wait_for_idle_c {
    wait_for_idle dist {
      1       :/ 1,
      0       :/ 10
    };
  }

  constraint weight_to_skip_rx_read_c {
    // 3: read, 7: skip
    weight_to_skip_rx_read == 7;
  }

  constraint dly_to_rx_read_c {
    dly_to_rx_read dist {0           :/ 1,
                         [1:100]     :/ 1,
                         [100:10000] :/ 2};
  }

  `uvm_object_new


  task pre_start();
    super.pre_start();
    num_trans.rand_mode(0);
    // dly to send a_valid is controlled in uart vseq level. Don't add additional delay in tl
    // driver as it may make tl happens at ignore period
    cfg.m_tl_agent_cfg.a_valid_delay_min = 0;
    cfg.m_tl_agent_cfg.a_valid_delay_max = 0;
  endtask

  task body();
    fork
      begin
        while (do_interrupt) process_interrupts();
      end
      begin
        // repeat test sequencing upto 50 times
        for (int i = 1; i <= num_trans; i++) begin
          // start each new run by randomizing dut parameters
          `DV_CHECK_RANDOMIZE_FATAL(this)

          uart_init();

          `uvm_info(`gfn, $sformatf("starting run %0d/%0d", i, num_trans), UVM_MEDIUM)
          fork
            begin
              `uvm_info(`gfn, $sformatf("begin sending %0d tx bytes", num_tx_bytes), UVM_MEDIUM)
              process_tx();
              `uvm_info(`gfn, $sformatf("done sending %0d tx bytes", num_tx_bytes), UVM_HIGH)
            end
            begin
              `uvm_info(`gfn, $sformatf("begin sending %0d rx bytes", num_rx_bytes), UVM_MEDIUM)
              process_rx();
              `uvm_info(`gfn, $sformatf("done sending %0d rx bytes", num_rx_bytes), UVM_HIGH)
            end
          join

          process_remaining_data();
          `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
        end
        do_interrupt = 0; // to end thread process_interrupts gracefully
      end
    join
  endtask : body

  task post_start();
    bit [TL_DW-1:0] intr_status;
    // dut_shutdown is must for each iteration, it's called in body
    do_dut_shutdown = 0;
    // need to clear fifo when tx is disabled as data isn't sent out
    if (ral.ctrl.tx.get_mirrored_value() == 0) begin
      clear_fifos(.clear_tx_fifo(1), .clear_rx_fifo(0));
      // wait for 1 cycle to allow tx_empty occur and be cleared later at super.post_start()
      cfg.clk_rst_vif.wait_clks(1);
    end
    super.post_start();
  endtask

  // read interrupts and randomly clear interrupts if set
  task process_interrupts();
    bit [TL_DW-1:0] intr_status, clear_intr;
    bit clear_rx_intr, clear_tx_intr;

    // avoid zero delay loop during reset
    wait(!cfg.under_reset);
    // read interrupt
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);
    csr_rd(.ptr(ral.intr_state), .value(intr_status));

    // clear interrupt, randomly clear the interrupt that is set, and
    // don't clear the interrupt which isn't set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clear_intr,
                                       foreach (clear_intr[i]) {
                                           clear_intr[i] -> intr_status[i] == 1;
                                       })
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_intr)
    cfg.clk_rst_vif.wait_clks(dly_to_access_intr);

    // for fifo interrupt, parity/frame error, don't clear it at ignored period
    // as it hasn't been checked
    clear_tx_intr = clear_intr[TxWatermark] | clear_intr[TxWatermark] | clear_intr[TxEmpty];
    clear_rx_intr = clear_intr[RxWatermark] | clear_intr[RxOverflow] | clear_intr[RxFrameErr] |
                    clear_intr[RxParityErr];
    wait_when_in_ignored_period(clear_tx_intr, clear_rx_intr);
    csr_wr(.ptr(ral.intr_state), .value(clear_intr));
  endtask

  virtual task process_tx();
    for (int j = 1; j <= num_tx_bytes; j++) begin
      byte tx_byte;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_trans)
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wait_for_idle)

      cfg.clk_rst_vif.wait_clks(dly_to_next_trans);
      wait_for_tx_fifo_not_full();
      wait_when_in_ignored_period(.tx(1));
      `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
      send_tx_byte(tx_byte);
      if (wait_for_idle) spinwait_txidle();
    end
  endtask : process_tx

  // control RX data from both sides independently
  //   1. uart device
  //   2. register
  virtual task process_rx();
    bit send_rx_done = 0;
    fork
      begin // drive from uart RX interface
        for (int j = 1; j <= num_rx_bytes; j++) begin
          byte rx_byte;
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_next_trans)
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wait_for_idle)
          `DV_CHECK_STD_RANDOMIZE_FATAL(rx_byte)

          cfg.clk_rst_vif.wait_clks(dly_to_next_trans);
          wait_for_rx_fifo_not_full();
          send_rx_byte(rx_byte);
          if (wait_for_idle) spinwait_rxidle();
        end
        send_rx_done = 1; // to end reading RX thread
      end
      begin // read RX data through register
        while (!send_rx_done && !cfg.under_reset) begin
          // csr read is much faster than uart transfer, use bigger delay
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_rx_read)
          cfg.clk_rst_vif.wait_clks(dly_to_rx_read);
          rand_read_rx_byte(weight_to_skip_rx_read);
        end
      end
    join
  endtask : process_rx

  virtual task process_remaining_data();

    fork
      begin // TX
        wait_for_all_tx_bytes();
        // tx fifo is empty but still need to wait for last tx item to be flushed out
        cfg.m_uart_agent_cfg.vif.wait_for_tx_idle();
      end
      begin // RX
        // wait for last rx item to be completed before read all of them
        cfg.m_uart_agent_cfg.vif.wait_for_rx_idle();
        read_all_rx_bytes();
      end
    join

  endtask : process_remaining_data

endclass : uart_tx_rx_vseq
