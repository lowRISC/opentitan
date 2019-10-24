// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_fifo_reset_vseq extends uart_fifo_overflow_vseq;
  `uvm_object_utils(uart_fifo_reset_vseq)

  `uvm_object_new

  virtual task process_remaining_data();
    bit do_clear_tx_fifo;
    bit do_clear_rx_fifo;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(do_clear_tx_fifo,
                                       do_clear_tx_fifo dist {0 :/ 1, 1 :/ 4};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(do_clear_rx_fifo,
                                       do_clear_rx_fifo dist {0 :/ 1, 1 :/ 4};)

    fork
      begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(dly_to_access_fifo)
        cfg.clk_rst_vif.wait_clks(dly_to_access_fifo);
        // can't predict if the item is clear or not, when reset fifo at almost done period
        wait_when_in_ignored_period(.tx(do_clear_tx_fifo), .rx(do_clear_rx_fifo));
        clear_fifos(.clear_tx_fifo(do_clear_tx_fifo), .clear_rx_fifo(do_clear_rx_fifo));
      end
      begin
        if (!do_clear_tx_fifo) begin
          wait_for_all_tx_bytes();
        end else begin
          spinwait_txidle();
        end
      end
      begin
        if (!do_clear_rx_fifo) begin
          read_all_rx_bytes();
        end else begin
          spinwait_rxidle();
        end
      end
    join

    dut_shutdown();
  endtask : process_remaining_data

endclass : uart_fifo_reset_vseq
