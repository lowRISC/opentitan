// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test rx parity error
// cross rx/tx watermark/overflow with parity error in this seq
class uart_rx_parity_err_vseq extends uart_fifo_overflow_vseq;
  `uvm_object_utils(uart_rx_parity_err_vseq)

  `uvm_object_new

  virtual task send_rx_byte(byte data);
    cfg.m_uart_agent_cfg.en_rx_checks = 0; // disable rx checks in monitor
    drive_rx_error_byte(.parity_err($urandom_range(0, 9) == 0), // 10%
                        .frame_err (0),
                        .data      (data));
    cfg.m_uart_agent_cfg.en_rx_checks = 1;
  endtask

endclass : uart_rx_parity_err_vseq
