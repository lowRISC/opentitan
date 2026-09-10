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
// - Luca Colagrande <colluca@iis.ee.ethz.ch>

`include "prim_assert.sv"

// Stream join dynamic: Joins a parametrizable number of input streams (i.e. valid-ready
// handshaking with dependency rules as in AXI4) to a single output stream. The subset of streams
// to join can be configured dynamically via `sel_i`. The output handshake happens only after
// there has been a handshake. The data channel flows outside of this module.
module stream_join_dynamic #(
  /// Number of input streams
  parameter int unsigned N_INP = 32'd0 // Synopsys DC requires a default value for parameters.
) (
  /// Input streams valid handshakes
  input  logic [N_INP-1:0] inp_valid_i,
  /// Input streams ready handshakes
  output logic [N_INP-1:0] inp_ready_o,
  /// Selection mask for the output handshake
  input  logic [N_INP-1:0] sel_i,
  /// Output stream valid handshake
  output logic             oup_valid_o,
  /// Output stream ready handshake
  input  logic             oup_ready_i
);

  // Corner case when `sel_i` is all 0s should not generate valid
  assign oup_valid_o = &(inp_valid_i | ~sel_i) && |sel_i;
  for (genvar i = 0; i < N_INP; i++) begin : gen_inp_ready
    assign inp_ready_o[i] = oup_valid_o & oup_ready_i & sel_i[i];
  end

  `ASSERT_INIT(NumInputLargerZero_A, N_INP >= 1)

endmodule
