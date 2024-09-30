// Copyright 2023 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

package secure_subsystem_synth_astral_pkg;

  localparam SynthAxiAddrWidth    = 64;
  localparam SynthAxiOutIdWidth   = 8;
  localparam SynthAxiUserWidth    = 1;
  localparam SynthAxiDataWidth    = 64;

  localparam SynthOtAxiAddrWidth  = 64;
  localparam SynthOtAxiOutIdWidth = 6;
  localparam SynthOtAxiUserWidth  = 1;
  localparam SynthOtAxiDataWidth  = 64;

  localparam SynthClsAxiIdWidth = 4;

  typedef logic [SynthAxiAddrWidth-1:0]     synth_axi_addr_t;
  typedef logic [SynthAxiDataWidth-1:0]     synth_axi_data_t;
  typedef logic [SynthAxiDataWidth/8-1:0]   synth_axi_strb_t;
  typedef logic [SynthAxiUserWidth-1:0]     synth_axi_user_t;
  typedef logic [SynthAxiOutIdWidth-1:0]    synth_axi_out_id_t;

  typedef logic [SynthOtAxiAddrWidth-1:0]   synth_ot_axi_addr_t;
  typedef logic [SynthOtAxiDataWidth-1:0]   synth_ot_axi_data_t;
  typedef logic [SynthOtAxiDataWidth/8-1:0] synth_ot_axi_strb_t;
  typedef logic [SynthOtAxiUserWidth-1:0]   synth_ot_axi_user_t;
  typedef logic [SynthOtAxiOutIdWidth-1:0]  synth_ot_axi_out_id_t;

  `AXI_TYPEDEF_ALL(synth_axi_out, synth_axi_addr_t, synth_axi_out_id_t, synth_axi_data_t, synth_axi_strb_t, synth_axi_user_t)
  `AXI_TYPEDEF_ALL(synth_ot_axi_out, synth_ot_axi_addr_t, synth_ot_axi_out_id_t, synth_ot_axi_data_t, synth_ot_axi_strb_t, synth_ot_axi_user_t)

  localparam SynthLogDepth = 3;
  localparam SynthCdcSyncStages = 2;

  localparam SynthAsyncAxiOutAwWidth = (2**SynthLogDepth)*$bits(synth_axi_out_aw_chan_t);
  localparam SynthAsyncAxiOutWWidth  = (2**SynthLogDepth)*$bits(synth_axi_out_w_chan_t);
  localparam SynthAsyncAxiOutBWidth  = (2**SynthLogDepth)*$bits(synth_axi_out_b_chan_t);
  localparam SynthAsyncAxiOutArWidth = (2**SynthLogDepth)*$bits(synth_axi_out_ar_chan_t);
  localparam SynthAsyncAxiOutRWidth  = (2**SynthLogDepth)*$bits(synth_axi_out_r_chan_t);

  localparam AxiMaxOutTrans = 2;

//`endif
endpackage
