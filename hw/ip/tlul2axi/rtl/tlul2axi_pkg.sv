// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//  
 
`include "axi_typedef.svh"
`include "axi_assign.svh"

package tlul2axi_pkg;
   
  parameter int unsigned AXI_ID_WIDTH            = 8; 
  parameter int unsigned AXI_ADDR_WIDTH          = 64; 
  parameter int unsigned AXI_SLV_PORT_DATA_WIDTH = 32; 
  parameter int unsigned AXI_MST_PORT_DATA_WIDTH = 64; 
  parameter int unsigned AXI_USER_WIDTH          = 1; 
  parameter int unsigned AXI_MAX_READS           = 1; 
 
  typedef logic [AXI_ADDR_WIDTH-1:0]            addr_t;
  typedef logic [AXI_MST_PORT_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_MST_PORT_DATA_WIDTH/8-1:0] strb_t;

  typedef logic [AXI_ID_WIDTH-1:0] id_t                   ;
  typedef logic [AXI_MST_PORT_DATA_WIDTH-1:0] mst_data_t  ;
  typedef logic [AXI_MST_PORT_DATA_WIDTH/8-1:0] mst_strb_t;
  typedef logic [AXI_SLV_PORT_DATA_WIDTH-1:0] slv_data_t  ;
  typedef logic [AXI_SLV_PORT_DATA_WIDTH/8-1:0] slv_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;
     
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, mst_data_t, mst_strb_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, slv_data_t, slv_strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, mst_data_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, slv_data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_t, mst_w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_rsp_t, b_chan_t, mst_r_chan_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_t, slv_w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_rsp_t, b_chan_t, slv_r_chan_t)

endpackage 
   
