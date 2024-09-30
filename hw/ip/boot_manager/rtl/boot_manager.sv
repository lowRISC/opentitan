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
// Author: Maicol Ciani maicol.ciani@unibo.it
//
// Boot manager of Secure Domain. Consists of an FSM register file, one connecetd
// to the boot select pad. The other registers and the FSM drives the alternative
// path to the flash controller memory element to preload the code via JTAG.

module boot_manager import tlul_ot_pkg::*; (
   input               clk_i,
   input               rst_ni,
   // Ibex Direct Interface
   input               tlul_ot_pkg::tl_h2d_t bootmode_tl_i,
   output              tlul_ot_pkg::tl_d2h_t bootmode_tl_o,
   // Physical Emulated Flash Interface
   output logic        flash_write_o,
   output logic        flash_req_o,
   output logic [15:0] flash_addr_o,
   output logic [75:0] flash_wdata_o,
   output logic [75:0] flash_wmask_o,
   // Debug Mode Signal
   input  logic [1:0]  bootmode_i,
   output logic        datapath_o,
   output logic        cluster_fetch_en_o
);
   import boot_manager_regs_reg_pkg::*;
   boot_manager_regs_reg_pkg::boot_manager_regs_reg2hw_t reg2hw;
   boot_manager_regs_reg_pkg::boot_manager_regs_hw2reg_t hw2reg;

   enum logic [1:0] { IDLE , WRITE , WAIT } state_d, state_q;

   logic [31:0] payload_1;
   logic [31:0] payload_2;
   logic [31:0] payload_3;
   logic [31:0] address;
   logic        start;

   logic [75:0] flash_wdata;
   logic [15:0] flash_addr;
   logic        flash_req;

   logic        bootmode_tieoff;

   boot_manager_regs_reg_top flash_buffer (
      .clk_i,
      .rst_ni,
      .tl_i(bootmode_tl_i),
      .tl_o(bootmode_tl_o),
      .reg2hw,
      .hw2reg,
      .devmode_i(1'b0),
      .intg_err_o()
   );

   always_comb begin //: flash-phy-writes
     state_d = IDLE;
     flash_req = 1'b0;
     hw2reg.start.start.de = 1'b0;

     case(state_q)
        IDLE: begin
           if(start)
             state_d = WRITE;
           else
             state_d = IDLE;
        end
        WRITE: begin
           flash_req = 1'b1;
           state_d = WAIT;
        end
        WAIT: begin
           state_d = IDLE;
           hw2reg.start.start.de = 1'b1;
        end
        default: state_d = IDLE;
     endcase
   end

   assign hw2reg.pad_bootmode.pad_bootmode.de = 1'b1;
   assign hw2reg.pad_bootmode.pad_bootmode.d  = bootmode_i[0];
   assign bootmode_tieoff                     = bootmode_i[1];

   assign payload_1     = reg2hw.payload_1.q;
   assign payload_2     = reg2hw.payload_2.q;
   assign payload_3     = reg2hw.payload_3.q;
   assign address       = reg2hw.address.q;
   assign start         = reg2hw.start.start.q;

   assign flash_wmask_o = '1;
   assign flash_addr_o  = address[15:0];
   assign flash_req_o   = flash_req;
   assign flash_write_o = 1'b1;
   assign flash_wdata_o = {payload_1, payload_2, payload_3[31:20]};
   assign datapath_o    = reg2hw.datapath.datapath.q;
   assign cluster_fetch_en_o  = reg2hw.cluster.fetch_enable.q;

   assign hw2reg.start.start.d  = 1'b0;
   assign hw2reg.start.field1 = '0;
   assign hw2reg.pad_bootmode.field1 = '0;

   always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni)
         state_q  <= IDLE;
      else
         state_q  <= state_d;
   end

endmodule
