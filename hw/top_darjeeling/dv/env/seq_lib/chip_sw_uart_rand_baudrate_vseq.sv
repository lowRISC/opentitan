// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define CALC_NCO(baud_rate, nco_width, clk_freq_khz) \
      (longint'(baud_rate) * (2**(nco_width+4))) / (clk_freq_khz * 1000)

class chip_sw_uart_rand_baudrate_vseq extends chip_sw_uart_tx_rx_vseq;
  `uvm_object_utils(chip_sw_uart_rand_baudrate_vseq)

  `uvm_object_new

  localparam NCO_WIDTH = 16;

  int uart_clk_freq_khz;  // Use khz to avoid fractional value.

  rand baud_rate_e baud_rate;

  constraint baud_rate_c {
    // constrain nco not over nco width
    `CALC_NCO(baud_rate, NCO_WIDTH, uart_clk_freq_khz) < (1 << NCO_WIDTH);
    // only test 4 other speeds, <= 115k is slow which may take a few hours to complete the test
    baud_rate > BaudRate115200;
  }

  function void pre_randomize();
    super.pre_randomize();
    // IO frequency is 250MHz
    uart_clk_freq_khz = 250_000;
  endfunction

  function void post_randomize();
    super.post_randomize();
    cfg.uart_baud_rate = baud_rate;
  endfunction

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] uart_freq_arr[8] = {<<byte{64'(cfg.uart_baud_rate)}};

    super.cpu_init();
    sw_symbol_backdoor_overwrite("kUartBaudrateDV", uart_freq_arr);
    `uvm_info(`gfn, $sformatf(
              "Backdoor_overwrite: configure uart core clk %0d khz, baud_rate: %s",
              uart_clk_freq_khz,
              baud_rate.name
              ), UVM_LOW)
  endtask

  // When uart starts to send RX data, check if AST is using extclk if extclk is selected.
  virtual task send_uart_rx_data(int instance_num, int size = -1, bit random = 0);
    super.send_uart_rx_data(instance_num, size, random);
  endtask

endclass : chip_sw_uart_rand_baudrate_vseq
`undef CALC_NCO
