// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define CALC_NCO(baud_rate, nco_width, clk_freq_khz) \
  (baud_rate == BaudRate1p5Mbps && clk_freq_khz == 24_000) ? 16'hffff : \
      (longint'(baud_rate) * (2**(nco_width+4))) / (clk_freq_khz * 1000)

class chip_sw_uart_rand_baudrate_vseq extends chip_sw_uart_tx_rx_vseq;
  `uvm_object_utils(chip_sw_uart_rand_baudrate_vseq)

  `uvm_object_new

  localparam NCO_WIDTH = 16;

  // Clkmgr external clock settings.
  bit use_extclk = 0;
  bit extclk_low_speed_sel = 0;

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
    void'($value$plusargs("use_extclk=%0d", use_extclk));
    void'($value$plusargs("extclk_low_speed_sel=%0d", extclk_low_speed_sel));
    if (use_extclk) begin
      // Uart bus clock is in div4 domain
      uart_clk_freq_khz = cfg.clk_freq_mhz * 1000 / 4;

      if (extclk_low_speed_sel) uart_clk_freq_khz = uart_clk_freq_khz * 2;
    end else begin
      // internal uart bus clock is 24Mhz
      uart_clk_freq_khz = 24_000;
    end
    `uvm_info(`gfn, $sformatf(
              "External clock freq: %0dmhz, use_extclk: %0d, extclk_low_speed_sel: %0d",
              cfg.clk_freq_mhz,
              use_extclk,
              extclk_low_speed_sel
              ), UVM_LOW)
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    cfg.uart_baud_rate = baud_rate;
  endtask

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

    if (use_extclk) begin
      bit [7:0] use_extclk_arr[] = {use_extclk};
      bit [7:0] low_speed_sel_arr[] = {extclk_low_speed_sel};
      bit [7:0] uart_clk_freq_arr[8] = {<<byte{uart_clk_freq_khz * 1000}};

      sw_symbol_backdoor_overwrite("kUseExtClk", use_extclk_arr);

      sw_symbol_backdoor_overwrite("kUseLowSpeedSel", low_speed_sel_arr);

      // SW relies on kClockFreqPeripheralHz to calcuate NCO and it's hard-coded to 24Mhz in SW.
      // this value is changed when extclk is used
      sw_symbol_backdoor_overwrite("kClockFreqPeripheralHz", uart_clk_freq_arr);
    end
  endtask

  // When uart starts to send RX data, check if AST is using extclk if extclk is selected.
  virtual task send_uart_rx_data(int size = -1, bit random = 0);
    if (use_extclk) begin
      `DV_CHECK(cfg.ast_ext_clk_vif.is_ext_clk_in_use(),
                "expected the external clock to be used for io");
    end
    super.send_uart_rx_data(size, random);
  endtask

endclass : chip_sw_uart_rand_baudrate_vseq
`undef CALC_NCO
