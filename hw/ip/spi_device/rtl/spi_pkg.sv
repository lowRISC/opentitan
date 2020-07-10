// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Define SPI interface
//


package spi_pkg;

  // SPI_DEVICE to SPI_HOST
  // single write only
  typedef struct packed {
    logic csb;
    logic s;
    logic s_en;
  } spi_d2h_t;

  parameter spi_d2h_t SPI_D2H_DEFAULT = '{
    csb: 1'b1,
    default: '0
  };

  typedef struct packed {
    logic [3:0] s;
  } spi_h2d_t;

  parameter spi_h2d_t SPI_H2D_DEFAULT = '{
    default: '0
  };

endpackage
