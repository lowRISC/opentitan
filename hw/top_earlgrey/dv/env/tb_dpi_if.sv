// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface is used to connect the dpi sequence to the dpi modules in tb.

interface tb_dpi_if();

  // Bit default value is 0, so dpi will be disabled until enable_all is called.
  bit enable_gpiodpi;
  bit enable_uartdpi;

  function automatic void enable_all();
    enable_gpiodpi = 1'b1;
    enable_uartdpi = 1'b1;
  endfunction

endinterface : tb_dpi_if
