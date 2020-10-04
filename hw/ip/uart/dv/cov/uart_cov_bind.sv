// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds UART functional coverage interaface to the top level UART module.
module uart_cov_bind;

  bind uart uart_cov_if u_uart_cov_if (.*);

  bind uart_core uart_core_cov_if u_uart_core_cov_if (.*);

endmodule
