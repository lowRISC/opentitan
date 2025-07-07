// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package soc_proxy_pkg;

  localparam int unsigned NumSocGpio = 16;

  // Keep this value in sync with pinmux and top-level configuration.
  localparam int unsigned NumSocGpioMappedOnDio = 12;
  localparam int unsigned NumSocGpioMuxed = NumSocGpio - NumSocGpioMappedOnDio;

endpackage
