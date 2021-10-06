// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define CALC_NCO(baud_rate, nco_width, clk_freq_mhz) \
  (baud_rate == BaudRate1p5Mbps && clk_freq_mhz == 24) ? 16'hffff : \
      (longint'(baud_rate) * (2**(nco_width+4))) / (clk_freq_mhz * 1000_000)

class chip_sw_uart_rand_baudrate_vseq extends chip_sw_uart_tx_rx_vseq;
  `uvm_object_utils(chip_sw_uart_rand_baudrate_vseq)

  `uvm_object_new

  localparam NCO_WIDTH = 16;

  rand baud_rate_e baud_rate;
  rand int uart_clk_freq_mhz = 24;

  // Use the fixed 24Mhz, override it in extended vseq
  constraint uart_clk_freq_mhz_c {
    uart_clk_freq_mhz == 24;
  }

  constraint baud_rate_c {
    // constrain nco not over nco width
    `CALC_NCO(baud_rate, NCO_WIDTH, uart_clk_freq_mhz) < (1 << NCO_WIDTH);
  }

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.uart_baud_rate = baud_rate;
  endtask

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] uart_freq[8] = {<< byte {cfg.uart_baud_rate}};

    super.cpu_init();
    $display("wcy0 %p", uart_freq);
    sw_symbol_backdoor_overwrite("kUartBaudrate", uart_freq);
    `uvm_info(`gfn, $sformatf("Configure uart core clk %0d Mhz, baud_rate: %s",
              uart_clk_freq_mhz, baud_rate.name), UVM_LOW)

  endtask

endclass : chip_sw_uart_rand_baudrate_vseq
`undef CALC_NCO
