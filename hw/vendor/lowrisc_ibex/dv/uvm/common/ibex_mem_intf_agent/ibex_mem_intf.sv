// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_mem_intf#(parameter int ADDR_WIDTH = 32,
                         parameter int DATA_WIDTH = 32);

  logic                    clock;
  logic                    reset;
  logic                    request;
  logic                    grant;
  logic [ADDR_WIDTH-1:0]   addr;
  logic                    we;
  logic [DATA_WIDTH/8-1:0] be;
  logic                    rvalid;
  logic [DATA_WIDTH-1:0]   wdata;
  logic [DATA_WIDTH-1:0]   rdata;
  logic                    error;

endinterface : ibex_mem_intf
