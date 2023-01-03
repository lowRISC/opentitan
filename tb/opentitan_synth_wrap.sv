// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

module opentitan_synth_wrap
   import axi_pkg::*;
   import jtag_pkg::*;
   import tlul2axi_pkg::*;
   import dm_ot::*;
   import lc_ctrl_pkg::*;
   #(
   parameter RomCtrlBootRomInitFile = "/scratch/mciani/he-soc/hardware/working_dir/opentitan/hw/top_earlgrey/sw/tests/hello_test/bootrom.vmem",
   parameter OtpCtrlMemInitFile = "/scratch/mciani/he-soc/hardware/working_dir/opentitan/hw/top_earlgrey/sw/tests/hello_test/otp-img.mem",
   parameter AW = 64,
   parameter DW = 64,
   parameter IW = 8,
   parameter UW = 1,
   parameter SW = DW/8,
   parameter type axi_addr_t = logic [AW-1:0],
   parameter type axi_data_t = logic [DW-1:0],
   parameter type axi_strb_t = logic [DW/8-1:0],
   parameter type axi_id_t = logic [IW-1:0],
   parameter type axi_user_t = logic [UW-1:0]

)  (
   
   input logic		 clk_i,
    
   input logic		 por_n_i,
   input logic		 irq_ibex_i,

   // JTAG port
   input logic		 jtag_tck_i,
   input logic		 jtag_tms_i,
   input logic		 jtag_trst_n_i,
   input logic		 jtag_tdi_i,
   output logic		 jtag_tdo_o,
   output logic		 jtag_tdo_oe_o,

   //AXI AR channel
   output logic [IW-1:0] ar_id_o,
   output logic [AW-1:0] ar_addr_o,
   output logic [7:0]	 ar_len_o,
   output logic [2:0]	 ar_size_o,
   output logic [1:0]	 ar_burst_o,
   output logic		 ar_lock_o,
   output logic [3:0]	 ar_cache_o,
   output logic [2:0]	 ar_prot_o,
   output logic [3:0]	 ar_qos_o,
   output logic [3:0]	 ar_region_o,
   output logic [UW-1:0] ar_user_o,
   output logic		 ar_valid_o,
   input logic		 ar_ready_i,

   //AXI AW channel
   output logic [IW-1:0] aw_id_o,
   output logic [AW-1:0] aw_addr_o,
   output logic [7:0]	 aw_len_o,
   output logic [2:0]	 aw_size_o,
   output logic [1:0]	 aw_burst_o,
   output logic		 aw_lock_o,
   output logic [3:0]	 aw_cache_o,
   output logic [2:0]	 aw_prot_o,
   output logic [3:0]	 aw_qos_o,
   output logic [3:0]	 aw_region_o,
   output logic [5:0]	 aw_atop_o,
   output logic [UW-1:0] aw_user_o,
   output logic		 aw_valid_o,
   input logic		 aw_ready_i,

   //AXI W channel
   output logic [DW-1:0] w_data_o,
   output logic [SW-1:0] w_strb_o,
   output logic		 w_last_o,
   output logic [UW-1:0] w_user_o,
   output logic		 w_valid_o,
   input logic		 w_ready_i,

   //AXI B channel
   input logic [IW-1:0]	 b_id_i,
   input logic [1:0]	 b_resp_i,
   input logic [UW-1:0]	 b_user_i,
   input logic		 b_valid_i,
   output logic		 b_ready_o,

   //AXI R channel
   input logic [IW-1:0]	 r_id_i,
   input logic [DW-1:0]	 r_data_i,
   input logic [1:0]	 r_resp_i,
   input logic		 r_last_i,
   input logic [UW-1:0]	 r_user_i,
   input logic		 r_valid_i,
   output logic		 r_ready_o
);
/*
   `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, axi_addr_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_W_CHAN_T(w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
   `AXI_TYPEDEF_B_CHAN_T(b_chan_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, axi_addr_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_R_CHAN_T(r_chan_t, axi_data_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
   `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)
   
   axi_req_t  axi_req;
   axi_resp_t axi_rsp;
  */

   tlul2axi_pkg::slv_req_t axi_req;
   tlul2axi_pkg::slv_rsp_t axi_rsp;

   jtag_pkg::jtag_req_t jtag_i;
   jtag_pkg::jtag_rsp_t jtag_o;

   //Unwrapping JTAG strucutres

   assign jtag_i.tck    = jtag_tck_i;
   assign jtag_i.tms    = jtag_tms_i;
   assign jtag_i.trst_n = jtag_trst_n_i;
   assign jtag_i.tdi    = jtag_tdi_i;
   
   assign jtag_tdo_o    = jtag_o.tdo;
   assign jtag_tdo_oe_o = jtag_o.tdo_oe;

   //Unwrapping AXI strucutres

   //AR channel
   assign ar_id_o     = axi_req.ar.id;
   assign ar_addr_o   = axi_req.ar.addr;
   assign ar_len_o    = axi_req.ar.len;
   assign ar_size_o   = axi_req.ar.size;
   assign ar_burst_o  = axi_req.ar.burst;
   assign ar_lock_o   = axi_req.ar.lock;
   assign ar_cache_o  = axi_req.ar.cache;
   assign ar_prot_o   = axi_req.ar.prot;
   assign ar_qos_o    = axi_req.ar.qos;
   assign ar_region_o = axi_req.ar.region;
   assign ar_user_o   = axi_req.ar.user;
   assign ar_valid_o  = axi_req.ar_valid;
   assign axi_rsp.ar_ready  = ar_ready_i;
   
   //AW channel
   assign aw_id_o     = axi_req.aw.id;
   assign aw_addr_o   = axi_req.aw.addr;
   assign aw_len_o    = axi_req.aw.len;
   assign aw_size_o   = axi_req.aw.size;
   assign aw_burst_o  = axi_req.aw.burst;
   assign aw_lock_o   = axi_req.aw.lock;
   assign aw_cache_o  = axi_req.aw.cache;
   assign aw_prot_o   = axi_req.aw.prot;
   assign aw_qos_o    = axi_req.aw.qos;
   assign aw_region_o = axi_req.aw.region;
   assign aw_atop_o   = axi_req.aw.atop;
   assign aw_user_o   = axi_req.aw.user;
   assign aw_valid_o  = axi_req.aw_valid;
   assign axi_rsp.aw_ready  = aw_ready_i;

   //W channel
   assign w_data_o    = axi_req.w.data;
   assign w_strb_o    = axi_req.w.strb;
   assign w_last_o    = axi_req.w.last;
   assign w_user_o    = axi_req.w.user;
   assign w_valid_o   = axi_req.w_valid;
   assign axi_rsp.w_ready = w_ready_i;

      //AXI B channel
   assign axi_rsp.b.id    = b_id_i;
   assign axi_rsp.b.resp  = b_resp_i;
   assign axi_rsp.b.user  = b_user_i;
   assign axi_rsp.b_valid = b_valid_i;
   assign b_ready_o = axi_req.b_ready;

   //AXI R channel
   assign axi_rsp.r.id    = r_id_i;
   assign axi_rsp.r.data  = r_data_i; 
   assign axi_rsp.r.resp  = r_resp_i;
   assign axi_rsp.r.last  = r_last_i;
   assign axi_rsp.r.user  = r_user_i;
   assign axi_rsp.r_valid = r_valid_i;
   assign r_ready_o = axi_req.r_ready;

   

   top_earlgrey #(
    .OtpCtrlMemInitFile(OtpCtrlMemInitFile),
    .RomCtrlBootRomInitFile(RomCtrlBootRomInitFile)
   ) u_RoT (
    .scan_rst_ni (rst_ni),
    .scan_en_i (1'b0),
    .scanmode_i (lc_ctrl_pkg::Off),
    .mio_in_i('0),
    .dio_in_i('0),
 //   .ast_clk_byp_ack_i(lc_ctrl_pkg::Off), 
    .all_clk_byp_ack_i(lc_ctrl_pkg::Off),
    .div_step_down_req_i(lc_ctrl_pkg::Off),
    .calib_rdy_i(lc_ctrl_pkg::Off),
    .io_clk_byp_ack_i(lc_ctrl_pkg::Off),
    .por_n_i ({por_n_i, por_n_i}),
    .clk_main_i (clk_i),
    .clk_io_i(clk_i),
    .clk_aon_i(clk_i),
    .axi_req_o(axi_req),
    .axi_rsp_i(axi_rsp),
    //.irq_ibex_i,
    .jtag_req_i(jtag_i),
    .jtag_rsp_o(jtag_o)
    );
   


endmodule
    
