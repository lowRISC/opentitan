// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import pattgen_agent_pkg::*;

interface pattgen_if;
  logic clk_i;
  logic rst_ni;

  // standard pattgen interface pins
  logic pda0_tx;
  logic pcl0_tx;
  logic pda1_tx;
  logic pcl1_tx;

  task automatic get_bit(string channel, bit polarity,
                         output bit bit_o);
    if (channel == "Channel0") begin
      if (!polarity) begin
        @(posedge pcl0_tx);
      end else begin
        @(negedge pcl0_tx);
      end
      bit_o = pda0_tx;
    end else if (channel == "Channel1") begin
      if (!polarity) begin
        @(posedge pcl1_tx);
      end else begin
        @(negedge pcl1_tx);
      end
      bit_o = pda1_tx;
    end else begin
      bit_o = 1'bx;
    end
  endtask : get_bit

endinterface : pattgen_if
