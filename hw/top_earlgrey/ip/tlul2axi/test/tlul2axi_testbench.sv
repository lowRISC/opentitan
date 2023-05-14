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

`include "../test/tlul_assign.svh"
`include "../test/axi_assign.svh"
`include "../test/axi_typedef.svh"

module tlul2axi_testbench #();

   localparam time TA   = 1ns;
   localparam time TT   = 2ns;
   localparam int unsigned RTC_CLOCK_PERIOD = 30.517us;

   logic rst_ni;
   logic clk_i;

   semaphore lock;
   
   import tlul_ot_pkg::*;
   import tlul_functions::*;
   

   parameter int   AW = 32;   
   parameter int   DW = 32;  
   parameter int   IW = 3;   
   parameter int   UW = 1;
   parameter bit   RAND_RESP = 0; 
   parameter int   AX_MIN_WAIT_CYCLES = 0;   
   parameter int   AX_MAX_WAIT_CYCLES = 3;   
   parameter int   R_MIN_WAIT_CYCLES = 0;   
   parameter int   R_MAX_WAIT_CYCLES = 3;   
   parameter int   RESP_MIN_WAIT_CYCLES = 0;
   parameter int   RESP_MAX_WAIT_CYCLES = 3;
   parameter int   NUM_BEATS = 100;

   localparam int unsigned SW = DW / 8;
   
   typedef logic [AW-1:0] axi_addr_t;
   typedef logic [DW-1:0] axi_data_t;
   typedef logic [IW-1:0] axi_id_t;
   typedef logic [SW-1:0] axi_strb_t;
   typedef logic [UW-1:0] axi_user_t;
      
   typedef tlul_functions::tlul_driver #( 
     .TT(TT), 
     .TA(TA)
   ) tlul_driver_t;
   
   typedef axi_test::axi_rand_slave #(  
     .AW(AW),
     .DW(DW),
     .IW(IW),
     .UW(UW),
     .TA(TA),
     .TT(TT),
     .RAND_RESP(RAND_RESP),
     .AX_MIN_WAIT_CYCLES(AX_MIN_WAIT_CYCLES),
     .AX_MAX_WAIT_CYCLES(AX_MAX_WAIT_CYCLES),
     .R_MIN_WAIT_CYCLES(R_MIN_WAIT_CYCLES),
     .R_MAX_WAIT_CYCLES(R_MAX_WAIT_CYCLES),
     .RESP_MIN_WAIT_CYCLES(RESP_MIN_WAIT_CYCLES),
     .RESP_MAX_WAIT_CYCLES(RESP_MAX_WAIT_CYCLES)
  ) axi_ran_slave;
   
   AXI_BUS #(
     .AXI_ADDR_WIDTH(AW),
     .AXI_DATA_WIDTH(DW),
     .AXI_ID_WIDTH(IW),
     .AXI_USER_WIDTH(UW)
   ) axi_slave ();

   AXI_BUS_DV #(
     .AXI_ADDR_WIDTH(AW),
     .AXI_DATA_WIDTH(DW),
     .AXI_ID_WIDTH(IW),
     .AXI_USER_WIDTH(UW)
   ) axi (clk_i);
   

   
   `AXI_TYPEDEF_AW_CHAN_T (axi_aw_t, axi_addr_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_W_CHAN_T  (axi_w_t, axi_data_t, axi_strb_t, axi_user_t)
   `AXI_TYPEDEF_B_CHAN_T  (axi_b_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_AR_CHAN_T (axi_ar_t, axi_addr_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_R_CHAN_T  (axi_r_t, axi_data_t, axi_id_t, axi_user_t)
   `AXI_TYPEDEF_REQ_T     (axi_req_t, axi_aw_t, axi_w_t, axi_ar_t)
   `AXI_TYPEDEF_RESP_T    (axi_resp_t, axi_b_t, axi_r_t)

   axi_req_t  axi_req;
   axi_resp_t axi_rsp;
     
   axi_ran_slave axi_rand_slave = new(axi);
   `AXI_ASSIGN (axi, axi_slave)

   tlul_ot_pkg::tl_h2d_t tl_req;
   tlul_ot_pkg::tl_d2h_t tl_rsp;
      
   tlul_bus tl_bus();
   tlul_driver_t tlul_master = new(tl_bus);
   
   `REQ_ASSIGN(tl_req, tl_bus.tl_req)
   `RSP_ASSIGN(tl_bus.tl_rsp, tl_rsp)

   `AXI_ASSIGN_FROM_REQ   (axi_slave, axi_req)
   `AXI_ASSIGN_TO_RESP    (axi_rsp, axi_slave)
   
   assign tl_bus.clk_i = clk_i;
    
   tlul2axi  #(
      .axi_req_t (axi_req_t),
      .axi_resp_t(axi_resp_t)
   ) u_dut (
      .clk_i,
      .rst_ni,           
      .tl_req,
      .tl_rsp,                   
      .axi_req,
      .axi_rsp
   );

   
   initial begin  : clock_rst_process
    lock = new(1);
    clk_i  = 1'b0;
    rst_ni = 1'b0;
    repeat (10)
      #(RTC_CLOCK_PERIOD/2) clk_i = 1'b0;
      rst_ni = 1'b1;
    forever
      #(RTC_CLOCK_PERIOD/2) clk_i = ~clk_i;
   end 
   
   initial begin  : axi_slave_process
      
    @(posedge rst_ni);
    axi_rand_slave.reset();
    repeat ($urandom_range(10,15)) @(posedge clk_i);

    axi_rand_slave.run();
      
   end

   initial begin  : axi_master_process
     
    @(posedge rst_ni);
    tlul_master.reset_master();
    repeat ($urandom_range(10,15)) @(posedge clk_i);

    repeat (NUM_BEATS) begin
       
      tlul_master.run(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
       
      if(tl_bus.tl_req.a_opcode == tlul_ot_pkg::Get) begin
        assert(tl_bus.tl_rsp.d_data == axi_rand_slave.drv.axi.r_data) else
          $fatal("Data mismatch - Read:  %0h expected: %0h", tl_bus.tl_rsp.d_data, axi_rand_slave.drv.axi.r_data);
      end else begin // if (tl_bus.tl_req.a_opcode == tlul_ot_pkg::PutFullData) 
        assert(tl_bus.tl_req.a_data == axi_rand_slave.drv.axi.w_data) else
          $fatal("Data mismatch - Wrote: %0h expected: %0h", tl_bus.tl_req.a_data, axi_rand_slave.drv.axi.w_data);
      end
       
    end 
      
    repeat ($urandom_range(10,15)) @(posedge clk_i);
    $finish;
   end 
   
endmodule
  
