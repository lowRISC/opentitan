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
// Design Name:    dm_sba_sva                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    SystemVerilog assertions for dm_sba                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module dm_sba_sva #(
  parameter int unsigned BusWidth = 32,
  parameter bit          ReadByteEnable = 1
)(
  input logic           clk_i,
  input logic           dmactive_i,
  input logic [2:0]     sbaccess_i,
  input dm::sba_state_e state_d
);

  ///////////////////////////////////////////////////////
  // Assertions
  ///////////////////////////////////////////////////////

  // maybe bump severity to $error if not handled at runtime
  dm_sba_access_size: assert property(@(posedge clk_i) disable iff (dmactive_i !== 1'b0)
      (state_d != dm::Idle) |-> (sbaccess_i < 4))
          else $warning ("accesses > 8 byte not supported at the moment");

endmodule: dm_sba_sva
