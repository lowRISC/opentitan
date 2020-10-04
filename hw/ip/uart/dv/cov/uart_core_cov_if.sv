// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for uart_core.sv sub-module.
interface uart_core_cov_if (
  input logic tx_enable,
  input logic rx_enable
);

  // This interface is bound to `uart_core` which is 1 level underneath `uart` which is the DUT top
  // level module.
  `DV_VIF_WRAP_SET_VIF(uart_core_cov_if, uart_core_cov_vif, 1)

endinterface
