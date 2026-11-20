// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package spi_host_env_cfg_pkg;
  // parameters

  // The number of chip select lines of the DUT.  Sim cfg variants can override it.
  `ifndef SPI_HOST_NUM_CS
    `define SPI_HOST_NUM_CS 1
  `endif
  parameter integer unsigned SPI_HOST_NUM_CS = `SPI_HOST_NUM_CS;
endpackage : spi_host_env_cfg_pkg
