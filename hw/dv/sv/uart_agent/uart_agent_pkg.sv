// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package uart_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // 1 start + 8 data + 1 stop
  parameter uint NUM_UART_XFER_BITS_WO_PARITY = 10;

  // local types
  typedef enum bit {
    UartTx,
    UartRx
  } uart_dir_e;

  // Max standard baudrate is 256000 bps in the link below, so 1M should be 1024000
  // Refer to www.ece.northwestern.edu/local-apps/matlabhelp/techdoc/matlab_external/baudrate.html
  typedef enum int {
    BaudRate9600    = 9600,
    BaudRate115200  = 115200,
    BaudRate230400  = 230400,
    BaudRate128Kbps = 128000,
    BaudRate256Kbps = 256000,
    BaudRate1Mbps   = 1000000,
    BaudRate1p5Mbps = 1500000
  } baud_rate_e;

  // functions
  function automatic real get_baud_rate_period_ns(baud_rate_e baud_rate);
    // return 10^9 / baud_rate ns upto 3 decimal places
    case(baud_rate)
      BaudRate9600  :  return 104166.667;
      BaudRate115200:  return 8680.556;
      BaudRate230400:  return 4340.278;
      BaudRate128Kbps: return 7812.5;
      BaudRate256Kbps: return 3906.25;
      BaudRate1Mbps :  return 1000;
      BaudRate1p5Mbps: return 666.667;
      default: `uvm_fatal("uart_agent_pkg", {"Unsupported baud_rate: ", baud_rate.name})
    endcase
  endfunction

  // package sources
  `include "uart_item.sv"
  `include "uart_agent_cfg.sv"
  `include "uart_agent_cov.sv"
  `include "uart_monitor.sv"
  `include "uart_driver.sv"
  `include "uart_sequencer.sv"
  `include "uart_logger.sv"
  `include "uart_agent.sv"
  `include "uart_seq_list.sv"

endpackage
