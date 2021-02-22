// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Arjan Bink - arjan.bink@silabs.com                         //
//                                                                            //
// Design Name:    dm_top_sva                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    SystemVerilog assertions for dm_top                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module dm_top_sva
#(
  parameter int unsigned        NrHarts          = 1,
  parameter int unsigned        BusWidth         = 32,
  parameter int unsigned        DmBaseAddress    = 'h1000,
  parameter logic [NrHarts-1:0] SelectableHarts  = {NrHarts{1'b1}},
  parameter bit                 ReadByteEnable   = 1
)(
  input logic           clk_i,
  input logic           rst_ni,
  input dm::hartinfo_t [NrHarts-1:0] hartinfo_i
);

  ///////////////////////////////////////////////////////
  // Assertions
  ///////////////////////////////////////////////////////

  // Check that BusWidth is supported
  bus_width: assert property (
      @(posedge clk_i) disable iff (!rst_ni)
          (1'b1) |-> (BusWidth == 32 || BusWidth == 64))
      else $fatal(1, "DM needs a bus width of either 32 or 64 bits");

  // Fail if the DM is not located on the zero page and one hart doesn't have two scratch registers.
  genvar i;
  generate for (i = 0; i < NrHarts; i++)
    begin
      hart_info: assert property (
          @(posedge clk_i) disable iff (!rst_ni)
              (1'b1) |-> ((DmBaseAddress > 0 && hartinfo_i[i].nscratch >= 2) || (DmBaseAddress == 0 && hartinfo_i[i].nscratch >= 1)))
          else $fatal(1, "If the DM is not located at the zero page each hart needs at least two scratch registers %d %d",i, hartinfo_i[i].nscratch);
    end
  endgenerate

endmodule: dm_top_sva
