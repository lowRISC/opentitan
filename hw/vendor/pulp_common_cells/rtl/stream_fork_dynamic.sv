// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "prim_assert.sv"

/// Dynamic stream fork: Connects the input stream (ready-valid) handshake to a combination of output
/// stream handshake.  The combination is determined dynamically through another stream, which
/// provides a bitmask for the fork.  For each input stream handshake, every output stream handshakes
/// exactly once. The input stream only handshakes when all output streams have handshaked, but the
/// output streams do not have to handshake simultaneously.
///
/// This module has no data ports because stream data does not need to be forked: the data of the
/// input stream can just be applied at all output streams.
module stream_fork_dynamic #(
  /// Number of output streams
  parameter int unsigned N_OUP = 32'd0 // Synopsys DC requires a default value for parameters.
) (
  /// Clock
  input  logic             clk_i,
  /// Asynchronous reset, active low
  input  logic             rst_ni,
  /// Input stream valid handshake,
  input  logic             valid_i,
  /// Input stream ready handshake
  output logic             ready_o,
  /// Selection mask for the output handshake
  input  logic [N_OUP-1:0] sel_i,
  /// Selection mask valid
  input  logic             sel_valid_i,
  /// Selection mask ready
  output logic             sel_ready_o,
  /// Output streams valid handshakes
  output logic [N_OUP-1:0] valid_o,
  /// Output streams ready handshakes
  input  logic [N_OUP-1:0] ready_i
);

  logic             int_inp_valid,  int_inp_ready;
  logic [N_OUP-1:0] int_oup_valid,  int_oup_ready;

  // Output handshaking
  for (genvar i = 0; i < N_OUP; i++) begin : gen_oups
    always_comb begin
      valid_o[i]       = 1'b0;
      int_oup_ready[i] = 1'b0;
      if (sel_valid_i) begin
        if (sel_i[i]) begin
          valid_o[i]       = int_oup_valid[i];
          int_oup_ready[i] = ready_i[i];
        end else begin
          int_oup_ready[i] = 1'b1;
        end
      end
    end
  end

  // Input handshaking
  always_comb begin
    int_inp_valid = 1'b0;
    ready_o       = 1'b0;
    sel_ready_o   = 1'b0;
    if (sel_valid_i) begin
      int_inp_valid = valid_i;
      ready_o       = int_inp_ready;
      sel_ready_o   = int_inp_ready;
    end
  end

  stream_fork #(
    .N_OUP  ( N_OUP )
  ) i_fork (
    .clk_i,
    .rst_ni,
    .valid_i ( int_inp_valid ),
    .ready_o ( int_inp_ready ),
    .valid_o ( int_oup_valid ),
    .ready_i ( int_oup_ready )
  );

  `ASSERT_INIT(NumOutputLargerZero_A, N_OUP >= 1)

endmodule
