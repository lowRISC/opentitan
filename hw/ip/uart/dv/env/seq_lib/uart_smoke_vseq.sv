// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// simple smoke test with both en_tx and en_rx on
// process one item at a time for TX and RX
class uart_smoke_vseq extends uart_tx_rx_vseq;
  `uvm_object_utils(uart_smoke_vseq)

  constraint num_trans_c {
    num_trans == 10;
  }

  constraint num_tx_bytes_c {
    num_tx_bytes == 5;
  }

  constraint num_rx_bytes_c {
    num_rx_bytes == 5;
  }

  constraint en_tx_c {
    en_tx == 1;
  }

  constraint en_rx_c {
    en_rx == 1;
  }

  `uvm_object_new

  task body();
    do_interrupt = 0;
    super.body();
  endtask : body

  // program one Tx item in register and wait for it to complete before send another one
  virtual task process_tx();
    for (int j = 1; j <= num_tx_bytes; j++) begin
      byte tx_byte;

      wait_when_in_ignored_period(.tx(1));
      `DV_CHECK_STD_RANDOMIZE_FATAL(tx_byte)
      send_tx_byte(tx_byte);
      // if no delay in TL-UL trans, DUT takes 1 more cycle to update status reg
      cfg.clk_rst_vif.wait_clks(1);
      spinwait_txidle();
    end
  endtask : process_tx

  // sequencally send one Rx byte, then immediately read from register and check it
  virtual task process_rx();
    for (int j = 1; j <= num_rx_bytes; j++) begin
      byte rx_byte;
      bit [TL_DW-1:0] dut_rdata;

      `DV_CHECK_STD_RANDOMIZE_FATAL(rx_byte)
      send_rx_byte(rx_byte);
      spinwait_rxidle();
      csr_rd(.ptr(ral.rdata), .value(dut_rdata));
      if (!cfg.under_reset) `DV_CHECK_EQ(rx_byte, dut_rdata)
    end
  endtask : process_rx

  virtual task process_remaining_data();
    dut_shutdown();
  endtask : process_remaining_data

endclass : uart_smoke_vseq
