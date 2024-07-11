// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Valente, University of Bologna
// Date: 18.06.2020
// Description: L2 subsystem

module crypto_sram_wrap
#(
  parameter int unsigned SlvNumWords  = 8192,
  parameter int unsigned SlvDataWidth = 32,
  parameter int unsigned NumMst       = 2,
  parameter int unsigned NumSlv       = 8,
  parameter int unsigned BankNumWords = SlvNumWords/NumSlv,
  parameter int unsigned SlvAddrWidth = $clog2(BankNumWords),
  parameter int unsigned MstAddrWidth = $clog2(SlvNumWords)
) (
  input  logic                                  clk_i,
  input  logic                                  rst_ni,

  input  logic [NumMst-1:0]                     req_i,
  input  logic [NumMst-1:0] [MstAddrWidth-1:0]  add_i,
  input  logic [NumMst-1:0]                     wen_i,
  input  logic [NumMst-1:0] [SlvDataWidth-1:0]  wdata_i,
  input  logic [NumMst-1:0] [3:0]               be_i,
  output logic [NumMst-1:0]                     gnt_o,
  output logic [NumMst-1:0]                     r_valid_o,
  output logic [NumMst-1:0] [SlvDataWidth-1:0]  r_rdata_o
);

  logic [NumSlv-1:0]                     mem_req_l2;
  logic [NumSlv-1:0]                     mem_wen_l2;
  logic [NumSlv-1:0]                     mem_gnt_l2;
  logic [NumSlv-1:0][SlvAddrWidth-1:0]   mem_addr_l2;
  logic [NumSlv-1:0][SlvDataWidth/8-1:0] mem_be_l2;
  logic [NumSlv-1:0][SlvDataWidth-1:0]   mem_wdata_l2;
  logic [NumSlv-1:0][SlvDataWidth-1:0]   mem_rdata_l2;

  tcdm_interconnect #(
    .NumIn        ( NumMst                     ),
    .NumOut       ( NumSlv                     ),
    .AddrWidth    ( MstAddrWidth               ),
    .DataWidth    ( SlvDataWidth               ),
    .AddrMemWidth ( SlvAddrWidth               ),
    .WriteRespOn  ( 1                          ),
    .RespLat      ( 1                          ),
    .Topology     ( tcdm_interconnect_pkg::LIC )
  ) i_tcdm_interconnect (
    .clk_i,
    .rst_ni,
    .req_i    ( req_i                        ),
    .add_i    ( add_i                        ),
    .wen_i    ( wen_i                        ),
    .wdata_i  ( wdata_i                      ),
    .be_i     ( be_i                         ),
    .gnt_o    ( gnt_o                        ),
    .vld_o    ( r_valid_o                    ),
    .rdata_o  ( r_rdata_o                    ),

    .req_o    ( mem_req_l2                         ),
    .gnt_i    ( mem_gnt_l2                         ),
    .add_o    ( mem_addr_l2                        ),
    .wen_o    ( mem_wen_l2                         ),
    .wdata_o  ( mem_wdata_l2                       ),
    .be_o     ( mem_be_l2                          ),
    .rdata_i  ( mem_rdata_l2                       )
  );

  for(genvar i=0; i<NumSlv; i++) begin : CUTS
     assign mem_gnt_l2[i] = mem_req_l2[i];
     tc_sram #(
       .SimInit   ( "random"            ),
       .NumWords  ( BankNumWords        ), // 2^10 lines of 32 bits each (4kB), 8 Banks -> 32kB total memory
       .DataWidth ( SlvDataWidth        ),
       .NumPorts  ( 1                   )
     ) bank_i (
       .clk_i,
       .rst_ni,
       .req_i   (  mem_req_l2[i]        ),
       .we_i    (  mem_wen_l2[i]        ),
       .addr_i  (  mem_addr_l2[i]       ),
       .wdata_i (  mem_wdata_l2[i]      ),
       .be_i    (  mem_be_l2[i]         ),
       .rdata_o (  mem_rdata_l2[i]      )
     );
  end

endmodule
