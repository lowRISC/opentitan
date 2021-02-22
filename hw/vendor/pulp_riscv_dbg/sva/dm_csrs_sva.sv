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
// Design Name:    dm_csrs_sva                                                //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    SystemVerilog assertions for dm_csrs                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module dm_csrs_sva #(
  parameter int unsigned        NrHarts          = 1,
  parameter int unsigned        BusWidth         = 32,
  parameter logic [NrHarts-1:0] SelectableHarts  = {NrHarts{1'b1}}
)(
  input logic           clk_i,
  input logic           rst_ni,
  input logic           dmi_req_valid_i,
  input logic           dmi_req_ready_o,
  input dm::dmi_req_t   dmi_req_i,
  input dm::dtm_op_e    dtm_op
);

  ///////////////////////////////////////////////////////
  // Assertions
  ///////////////////////////////////////////////////////

  haltsum: assert property (
      @(posedge clk_i) disable iff (!rst_ni)
          (dmi_req_ready_o && dmi_req_valid_i && dtm_op == dm::DTM_READ) |->
              !({1'b0, dmi_req_i.addr} inside
                  {dm::HaltSum0, dm::HaltSum1, dm::HaltSum2, dm::HaltSum3}))
      else $warning("Haltsums have not been properly tested yet.");

endmodule: dm_csrs_sva
