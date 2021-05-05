// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package uart_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import uart_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import uart_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types
  parameter uint UART_FIFO_DEPTH = 32;

  typedef enum int {
    TxWatermark = 0,
    RxWatermark = 1,
    TxEmpty     = 2,
    RxOverflow  = 3,
    RxFrameErr  = 4,
    RxBreakErr  = 5,
    RxTimeout   = 6,
    RxParityErr = 7,
    NumUartIntr = 8
  } uart_intr_e;

  // get the number of bytes that triggers watermark interrupt
  function automatic int get_watermark_bytes_by_level(int lvl, uart_dir_e dir);
    case(lvl)
      0: return dir == UartTx ? 2 : 1;
      1: return 4;
      2: return 8;
      3: return 16;
      4: return 30;
      default: begin
        `uvm_fatal("uart_env_pkg::get_watermark_bytes_by_level",
                   $sformatf("invalid watermark level value - %0d", lvl))
      end
    endcase
  endfunction

  // get the number of bytes that triggers break interrupt
  function automatic int get_break_bytes_by_level(int lvl);
    case(lvl)
      0: return 2;
      1: return 4;
      2: return 8;
      3: return 16;
      default: begin
        `uvm_fatal("uart_env_pkg::get_break_bytes_by_level",
                   $sformatf("invalid break level value - %0d", lvl))
      end
    endcase
  endfunction

  // nco = 16*(2 ** nco_width) * freq_baud / freq_core, and truncate the factional number
  // if uart baud rate is 1500_000 and IO is 24Mhz, NCO is 'h1_0000, which is over the NCO width
  // use NCO = 'hffff for this case since the error is tolerable. Refer to #4263
  `define CALC_NCO(baud_rate, nco_width, clk_freq_mhz) \
    (baud_rate == BaudRate1p5Mbps && clk_freq_mhz == ClkFreq24Mhz) ? 16'hffff : \
        (longint'(baud_rate) * (2**(nco_width+4))) / (clk_freq_mhz * 1000_000)

  // calculate the nco
  function automatic int get_nco(baud_rate_e baud_rate, int clk_freq_mhz, int nco_width);
    int nco;
    nco = `CALC_NCO(baud_rate, nco_width, clk_freq_mhz);
    if (nco >= (2 ** nco_width)) begin
      `uvm_fatal("uart_agent_pkg::get_nco", $sformatf(
                 {"nco (%0d) can't bigger than (2 ** %0d) - 1, it's only %0d bits ",
                  "baud_rate = %0d, clk_freq_mhz = %0d"},
                 nco, nco_width, nco_width, baud_rate, clk_freq_mhz))
    end
    return nco;
  endfunction

  // TX finishes the item at the beginning of last cycle and update reg value
  // in the last 2 cycles, need to avoid driving and checking
  `define TX_IGNORED_PERIOD {1, 2}
  // RX finishes the item at the middle of last cycle and update reg value
  // in the last cycle, need to avoid driving and checking
  `define RX_IGNORED_PERIOD {1}

  // package sources
  `include "uart_env_cfg.sv"
  `include "uart_env_cov.sv"
  `include "uart_virtual_sequencer.sv"
  `include "uart_scoreboard.sv"
  `include "uart_env.sv"
  `include "uart_vseq_list.sv"

  `undef CALC_NCO
  `undef TX_IGNORED_PERIOD
  `undef RX_IGNORED_PERIOD
endpackage
