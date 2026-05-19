// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Stream fork: Connects the input stream (ready-valid) handshake to *all* of `N_OUP` output stream
// handshakes. For each input stream handshake, every output stream handshakes exactly once. The
// input stream only handshakes when all output streams have handshaked, but the output streams do
// not have to handshake simultaneously.
//
// This module has no data ports because stream data does not need to be forked: the data of the
// input stream can just be applied at all output streams.

`include "prim_assert.sv"

module stream_fork #(
    parameter int unsigned N_OUP = 0    // Synopsys DC requires a default value for parameters.
) (
    input  logic                clk_i,
    input  logic                rst_ni,
    input  logic                valid_i,
    output logic                ready_o,
    output logic [N_OUP-1:0]    valid_o,
    input  logic [N_OUP-1:0]    ready_i
);

    typedef enum logic {READY, WAITING} state_t;

    logic [N_OUP-1:0]   oup_ready,
                        all_ones;

    state_t inp_state_d, inp_state_q;

    // Input control FSM
    always_comb begin
        // ready_o     = 1'b0;
        inp_state_d = inp_state_q;

        unique case (inp_state_q)
            READY: begin
                if (valid_i) begin
                    if (valid_o == all_ones && ready_i == all_ones) begin
                        // If handshake on all outputs, handshake on input.
                        ready_o = 1'b1;
                    end else begin
                        ready_o = 1'b0;
                        // Otherwise, wait for inputs that did not handshake yet.
                        inp_state_d = WAITING;
                    end
                end else begin
                    ready_o = 1'b0;
                end
            end
            WAITING: begin
                if (valid_i && oup_ready == all_ones) begin
                    ready_o = 1'b1;
                    inp_state_d = READY;
                end else begin
                    ready_o = 1'b0;
                end
            end
            default: begin
                inp_state_d = READY;
                ready_o = 1'b0;
            end
        endcase
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (!rst_ni) begin
            inp_state_q <= READY;
        end else begin
            inp_state_q <= inp_state_d;
        end
    end

    // Output control FSM
    for (genvar i = 0; i < N_OUP; i++) begin: gen_oup_state
        state_t oup_state_d, oup_state_q;

        always_comb begin
            oup_ready[i]    = 1'b1;
            valid_o[i]      = 1'b0;
            oup_state_d     = oup_state_q;

            unique case (oup_state_q)
                READY: begin
                    if (valid_i) begin
                        valid_o[i] = 1'b1;
                        if (ready_i[i]) begin   // Output handshake
                            if (!ready_o) begin     // No input handshake yet
                                oup_state_d = WAITING;
                            end
                        end else begin          // No output handshake
                            oup_ready[i] = 1'b0;
                        end
                    end
                end
                WAITING: begin
                    if (valid_i && ready_o) begin   // Input handshake
                        oup_state_d = READY;
                    end
                end
                default: begin
                    oup_state_d = READY;
                end
            endcase
        end

        always_ff @(posedge clk_i, negedge rst_ni) begin
            if (!rst_ni) begin
                oup_state_q <= READY;
            end else begin
                oup_state_q <= oup_state_d;
            end
        end
    end

    assign all_ones = '1;   // Synthesis fix for Vivado, which does not correctly compute the width
                            // of the '1 literal when assigned to a port of parametrized width.

    `ASSERT_INIT(NumOutputLargerZero_A, N_OUP >= 1)

endmodule
