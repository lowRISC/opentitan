// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Robert Balas <balasr@iis.ee.ethz.ch>
// Description: Bootrom for firmware booting

module boot_rom (
    input logic         clk_i,
    input logic         req_i,
    input logic [31:0]  addr_i,
    output logic [31:0] rdata_o
);
    localparam int          RomSize    = 2;
    localparam logic [31:0] entry_addr = 32'h1c00_0080;

    const logic [RomSize-1:0][31:0] mem = {
        dm_tb_pkg::jalr(5'h0, 5'h1, entry_addr[11:0]),
        dm_tb_pkg::lui(5'h1, entry_addr[31:12])
    };

  logic [$clog2(RomSize)-1:0]     addr_q;


  assign rdata_o = (addr_q < RomSize) ? mem[addr_q] : '0;

  always_ff @(posedge clk_i) begin
      if (req_i) begin
          addr_q <= addr_i[$clog2(RomSize)-1+3:2];
      end
  end

endmodule
