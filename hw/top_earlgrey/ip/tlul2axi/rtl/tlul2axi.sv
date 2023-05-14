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

module tlul2axi
  import tlul_ot_pkg::*;
  #(
    parameter int unsigned AXI_ID_WIDTH      = 8,
    parameter int unsigned AXI_ADDR_WIDTH    = 64,
    parameter int unsigned AXI_DATA_WIDTH    = 32,
    parameter int unsigned AXI_USER_WIDTH    = 1
   ) (
   input logic  clk_i,
   input logic  rst_ni,
    
   //  tlul host
   input        tl_h2d_t tl_i,
   output       tl_d2h_t tl_o,
      
   input logic  intr_mbox_irq_i,
   output logic intr_mbox_irq_o,
      
   //  axi master 
   input        tlul2axi_pkg::slv_rsp_t axi_rsp_i,
   output       tlul2axi_pkg::slv_req_t axi_req_o

   );
   
   enum  logic [2:0] { IDLE, WAIT_B_VALID, WAIT_R_VALID, WAIT_AR_READY, WAIT_AW_READY, WAIT_W_READY } state_q, state_d;

   assign intr_mbox_irq_o = intr_mbox_irq_i;
   
   tlul_ot_pkg::tl_d2h_t tl_o_int;
   
   tlul_rsp_intg_gen #(
     .EnableRspIntgGen(1),
     .EnableDataIntgGen(1)
   ) u_rsp_intg_gen (
     .tl_i(tl_o_int),
     .tl_o(tl_o)
   );
   always_comb  begin

    state_d = state_q; 

    case(state_q)

      IDLE: begin
        if(axi_req_o.ar_valid)       
          if(axi_rsp_i.ar_ready)
            state_d = WAIT_R_VALID;
          else
            state_d = WAIT_AR_READY;
        if(axi_req_o.aw_valid && axi_req_o.w_valid)
          case({axi_rsp_i.aw_ready, axi_rsp_i.w_ready})
            2'b01:   state_d = WAIT_AW_READY;
            2'b10:   state_d = WAIT_W_READY;
            2'b11:   state_d = WAIT_B_VALID;
            default: state_d = IDLE;
          endcase 
      end // case: IDLE

      WAIT_AW_READY: begin
         if(axi_rsp_i.aw_ready)
           state_d = WAIT_B_VALID;
         else
           state_d = WAIT_AW_READY;
      end

      WAIT_AR_READY: begin
         if(axi_rsp_i.ar_ready)
           state_d = WAIT_R_VALID;
         else
           state_d = WAIT_AR_READY;
      end

      WAIT_W_READY: begin
         if(axi_rsp_i.w_ready)
           state_d = WAIT_B_VALID;
         else
           state_d = WAIT_W_READY;
      end

      WAIT_R_VALID: begin
        if(axi_rsp_i.r_valid && axi_req_o.r_ready) 
          state_d = IDLE;
        else
          state_d = WAIT_R_VALID;
      end

      
      WAIT_B_VALID: begin
        if(axi_rsp_i.b_valid && axi_req_o.b_ready) 
          state_d = IDLE;
        else
          state_d = WAIT_B_VALID;
      end

      default: state_d = IDLE;
      
    endcase // case (state_q)
      
   end
   
     
   always_comb begin : axi_mst_output_fsm
       
    // Default assignments
        
  
    axi_req_o.aw.addr   = { 32'b0, tl_i.a_address };
    axi_req_o.aw.prot   = 3'b0;
    axi_req_o.aw.region = 4'b0;
    axi_req_o.aw.len    = 8'b0;
    axi_req_o.aw.size   = { 1'b0 , tl_i.a_size };   
    axi_req_o.aw.burst  = axi_pkg::BURST_INCR; 
    axi_req_o.aw.lock   = 1'b0;
    axi_req_o.aw.cache  = 4'b0;
    axi_req_o.aw.qos    = 4'b0;
    axi_req_o.aw.id     = tl_i.a_source;
    axi_req_o.aw.atop   = '0;
    axi_req_o.aw.user   = '0;

   
    axi_req_o.ar.addr   = { 32'b0, tl_i.a_address };
    axi_req_o.ar.prot   = 3'b0;
    axi_req_o.ar.region = 4'b0;
    axi_req_o.ar.len    = 8'b0;
    axi_req_o.ar.size   = { 1'b0 , tl_i.a_size };
    axi_req_o.ar.burst  = axi_pkg::BURST_INCR; 
    axi_req_o.ar.lock   = 1'b0;
    axi_req_o.ar.cache  = 4'b0;
    axi_req_o.ar.qos    = 4'b0;
    axi_req_o.ar.id     = tl_i.a_source;
    axi_req_o.ar.user   = '0;
 
    axi_req_o.w.data    = '0;
    axi_req_o.w.strb    = '0;
    axi_req_o.w.user    = '0;

    tl_o_int.d_valid     = 1'b0;
    tl_o_int.d_opcode    = tlul_ot_pkg::AccessAck;
    tl_o_int.d_param     = '0;
    tl_o_int.d_size      = tl_i.a_size;
    tl_o_int.d_source    = '0;
    tl_o_int.d_sink      = '0;
    tl_o_int.d_data      = '0;
    tl_o_int.d_user      = tl_i.a_user;
    tl_o_int.d_error     = '0;
    tl_o_int.a_ready     = '0;

    axi_req_o.b_ready   = 1'b0;
    axi_req_o.r_ready   = 1'b0;
    axi_req_o.w_valid   = 1'b0;
    axi_req_o.aw_valid  = 1'b0;
    axi_req_o.w.last    = 1'b0;
    axi_req_o.ar_valid  = 1'b0;
      
    tl_o_int.a_ready = 1'b0;
    tl_o_int.d_valid = 1'b0;

    case (state_q)

      IDLE: begin
        if(tl_i.a_valid) begin        // request   
          if(tl_i.a_opcode == tlul_ot_pkg::Get) begin // get
            axi_req_o.ar_valid = 1'b1;
            if(axi_rsp_i.ar_ready)
              tl_o_int.a_ready = 1'b1; 
          end else if (tl_i.a_opcode == tlul_ot_pkg::PutFullData || tl_i.a_opcode == tlul_ot_pkg::PutPartialData) begin                                     
            axi_req_o.w.last   = 1'b1;
            axi_req_o.aw_valid = 1'b1;
            axi_req_o.w_valid  = 1'b1;
            axi_req_o.w.data = tl_i.a_data;
            axi_req_o.w.strb = tl_i.a_mask;
            if(axi_rsp_i.aw_ready && axi_rsp_i.w_ready)
              tl_o_int.a_ready = 1'b1;
          end                   
        end 
      end

      WAIT_AR_READY: begin 
          axi_req_o.ar_valid = 1'b1;
          if(axi_rsp_i.ar_ready)
            tl_o_int.a_ready = 1'b1;
      end

      WAIT_AW_READY: begin
         axi_req_o.aw_valid = 1'b1;  
         if(axi_rsp_i.aw_ready)
            tl_o_int.a_ready = 1'b1;
      end

      WAIT_W_READY: begin 
          axi_req_o.w.last   = 1'b1;
          axi_req_o.w_valid  = 1'b1;
          axi_req_o.w.data   = tl_i.a_data;
          axi_req_o.w.strb   = tl_i.a_mask;
          if(axi_rsp_i.w_ready)
            tl_o_int.a_ready = 1'b1;
      end

      WAIT_B_VALID: begin
        if(axi_rsp_i.b_valid) begin
          tl_o_int.d_source = axi_rsp_i.b.id;
          tl_o_int.d_opcode = tlul_ot_pkg::AccessAck;
          tl_o_int.d_error  = axi_rsp_i.b.resp[1];
          tl_o_int.d_valid  = 1'b1;
          axi_req_o.b_ready = 1'b1;
        end
      end

      WAIT_R_VALID: begin
        if(axi_rsp_i.r_valid) begin
          tl_o_int.d_source = axi_rsp_i.r.id;
          tl_o_int.d_opcode = tlul_ot_pkg::AccessAckData;
          tl_o_int.d_error  = axi_rsp_i.r.resp[1];
          tl_o_int.d_data   = axi_rsp_i.r.data;
          tl_o_int.d_valid  = 1'b1;
          axi_req_o.r_ready = 1'b1;
        end
      end

      default: begin
        axi_req_o.b_ready   = 1'b0;
        axi_req_o.r_ready   = 1'b0;
        axi_req_o.w_valid   = 1'b0;
        axi_req_o.aw_valid  = 1'b0;
        axi_req_o.w.last    = 1'b0;
        axi_req_o.ar_valid  = 1'b0;
      end
          
    endcase 
    
  end 

//----------------
// Registers
//----------------
   
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) 
       state_q  <= IDLE; //RESET
    else 
       state_q  <= state_d;
  end
   
endmodule // tlul2axi
