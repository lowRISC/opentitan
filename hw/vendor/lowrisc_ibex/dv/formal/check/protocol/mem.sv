// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following describes the protocol for the memory interface to Ibex, as defined by the documentation.

In this case all responses must be within bounded time (`TIME_BOUND cycles). Removing the bound
leaves some properties inconclusive.
*/

`define TIME_LIMIT 5

interface mem_assume_t(
    input logic clk_i,
    input logic rst_ni,

    input logic req_o,
    input logic gnt_i,
    input logic rvalid_i,
    input logic err_i
);
    logic [7:0] outstanding_reqs_q;
    logic [7:0] outstanding_reqs;
    assign outstanding_reqs = outstanding_reqs_q + gnt_i - rvalid_i;

    always @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            outstanding_reqs_q <= 0;
        end else begin
            outstanding_reqs_q <= outstanding_reqs;
        end
    end

    // Sail does not specify what happens on bus errors.
    NoErr: assume property (@(posedge clk_i) ~err_i);

    // 1. Only send an rvalid if there is an outstanding request, but not in this cycle
    MemValidBounded: assume property (@(posedge clk_i) outstanding_reqs_q == 8'b0 |-> ~rvalid_i);
    // 2. Grants can only be sent when they are requested
    MemGntOnRequest: assume property (@(posedge clk_i) ~req_o |-> ~gnt_i);

    // Grants must respond within TIME_LIMIT cycles
    GntBound: assume property (@(posedge clk_i) req_o |-> ##[0:`TIME_LIMIT] gnt_i);

    // RValid takes no more than TIME_LIMIT cycles
    MemValidTimer: assume property (
      @(posedge clk_i)
      outstanding_reqs != 0 |-> ##[0:`TIME_LIMIT] rvalid_i
    );

    // Responses have to come eventually, implied by the above bounds so removed
    // MemGntEventually: assume property (@(posedge clk_i) req_o |-> s_eventually gnt_i);
    // MemRespEventually: assume property (always (s_eventually (outstanding_reqs == 8'b0)));
endinterface
