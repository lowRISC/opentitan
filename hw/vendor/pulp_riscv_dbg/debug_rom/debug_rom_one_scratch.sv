/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: $filename.v
 *
 * Description: Auto-generated bootrom
 */

// Auto-generated code
module debug_rom_one_scratch (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         req_i,
  input  logic [63:0]  addr_i,
  output logic [63:0]  rdata_o
);

  localparam int unsigned RomSize = 14;

  logic [RomSize-1:0][63:0] mem;
  assign mem = {
    64'h7b200073_7b202473,
    64'h10802823_f1402473,
    64'haa5ff06f_7b202473,
    64'h10002423_00100073,
    64'h7b202473_10002c23,
    64'hfddff06f_fc0414e3,
    64'h00247413_40044403,
    64'hf1402473_02041263,
    64'h00147413_40044403,
    64'h10802023_f1402473,
    64'h7b241073_0ff0000f,
    64'h00000013_0380006f,
    64'h00000013_0580006f,
    64'h00000013_0180006f
  };

  logic [$clog2(RomSize)-1:0] addr_d, addr_q;

  assign addr_d = req_i ? addr_i[$clog2(RomSize)-1+3:3] : addr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_q <= '0;
    end else begin
      addr_q <= addr_d;
    end
  end

  // this prevents spurious Xes from propagating into
  // the speculative fetch stage of the core
  always_comb begin : p_outmux
    rdata_o = '0;
    if (addr_q < $clog2(RomSize)'(RomSize)) begin
      rdata_o = mem[addr_q];
    end
  end

endmodule
