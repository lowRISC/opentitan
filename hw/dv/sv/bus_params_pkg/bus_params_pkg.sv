// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package bus_params_pkg;

  // Set the bus address width.
`ifdef BUS_AW
  parameter int BUS_AW = `BUS_AW;
`else
  parameter int BUS_AW = top_pkg::TL_AW;
`endif

  // Set the bus data width.
`ifdef BUS_DW
  parameter int BUS_DW = `BUS_DW;
`else
  parameter int BUS_DW = top_pkg::TL_DW;
`endif

  // Set the bus data mask width (# of byte lanes).
`ifdef BUS_DBW
  parameter int BUS_DBW = `BUS_DBW;
`else
  parameter int BUS_DBW = top_pkg::TL_DBW;
`endif

  // Set the bus transfer size width (# of bits requred to select the # of bytes).
`ifdef BUS_SZW
  parameter int BUS_SZW = `BUS_SZW;
`else
  parameter int BUS_SZW = top_pkg::TL_SZW;
`endif

// Set the bus address info (source) width.
`ifdef BUS_AIW
  parameter int BUS_AIW = `BUS_AIW;
`else
  parameter int BUS_AIW = top_pkg::TL_AIW;
`endif

// Set the bus data info (source) width.
`ifdef BUS_DIW
  parameter int BUS_DIW = `BUS_DIW;
`else
  parameter int BUS_DIW = top_pkg::TL_DIW;
`endif

// Set the bus a channel user width.
`ifdef BUS_AUW
  parameter int BUS_AUW = `BUS_AUW;
`else
  parameter int BUS_AUW = top_pkg::TL_AUW;
`endif

// Set the bus d channel user width.
`ifdef BUS_DUW
  parameter int BUS_DUW = `BUS_DUW;
`else
  parameter int BUS_DUW = top_pkg::TL_DUW;
`endif


endpackage
