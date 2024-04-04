// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define CALC_NCO(baud_rate, nco_width, clk_freq_khz) \
  (baud_rate == BaudRate1p5Mbps && clk_freq_khz == 24_000) ? 16'hffff : \
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

    if (cfg.chip_clock_source != ChipClockSourceInternal) begin
      // Uart bus clock is in div4 domain
      uart_clk_freq_khz = cfg.chip_clock_source * 1000 / 4;  // div4
      if (cfg.chip_clock_source == ChipClockSourceExternal48Mhz) begin
        uart_clk_freq_khz = uart_clk_freq_khz * 2;  // div2
      end
    end else begin
      // internal uart bus clock is 24Mhz
      uart_clk_freq_khz = 24_000;
    end
  endfunction

  function void post_randomize();
    super.post_randomize();
    cfg.uart_baud_rate = baud_rate;
  endfunction

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] uart_freq_arr[8] = {<<byte{cfg.uart_baud_rate}};

    super.cpu_init();
    sw_symbol_backdoor_overwrite("kUartBaudrate", uart_freq_arr);
    `uvm_info(`gfn, $sformatf(
              "Backdoor_overwrite: configure uart core clk %0d khz, baud_rate: %s",
              uart_clk_freq_khz,
              baud_rate.name
              ), UVM_LOW)

    if (cfg.chip_clock_source != ChipClockSourceInternal) begin
      bit [7:0] use_extclk_arr[] = {cfg.chip_clock_source != ChipClockSourceInternal};
      bit [7:0] low_speed_sel_arr[] = {cfg.chip_clock_source == ChipClockSourceExternal48Mhz};
      bit [7:0] uart_clk_freq_arr[8] = {<<byte{uart_clk_freq_khz * 1000}};

      sw_symbol_backdoor_overwrite("kUseExtClk", use_extclk_arr);
      sw_symbol_backdoor_overwrite("kUseLowSpeedSel", low_speed_sel_arr);
      sw_symbol_backdoor_overwrite("kClockFreqPeripheralHz", uart_clk_freq_arr);
    end
  endtask

  // When uart starts to send RX data, check if AST is using extclk if extclk is selected.
  virtual task send_uart_rx_data(int instance_num, int size = -1, bit random = 0);
    if (cfg.chip_clock_source != ChipClockSourceInternal) begin
      `DV_CHECK(cfg.ast_ext_clk_vif.is_ext_clk_in_use(),
                "expected the external clock to be used for io");
    end
    super.send_uart_rx_data(instance_num, size, random);
  endtask

endclass : chip_sw_uart_rand_baudrate_vseq
`undef CALC_NCO
