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

`include "tlul_assign.svh"

package tlul_functions;
  import tlul_ot_pkg::*; 
  class tlul_driver#(
    parameter time         TA         = 0ns,    // application time
    parameter time         TT         = 0ns     // test time
  );
    
    virtual tlul_bus tl_bus;
    semaphore lock;
    logic clk_i;     

    function new(virtual tlul_bus tlbus, logic clk = 0);
      this.tl_bus = tlbus;  
      this.clk_i  = clk; 
      this.lock   = new(1);
    endfunction
   

    function void reset_master();
      
      tl_bus.tl_req.a_valid     <= '0;
      tl_bus.tl_req.a_opcode    <= tlul_ot_pkg::Get;
      tl_bus.tl_req.a_param     <= '0;
      tl_bus.tl_req.a_size      <= '0;
      tl_bus.tl_req.a_source    <= '0;
      tl_bus.tl_req.a_address   <= '0;
      tl_bus.tl_req.a_mask      <= '0;
      tl_bus.tl_req.a_data      <= '0;
      tl_bus.tl_req.a_user      <= '0;
      tl_bus.tl_req.d_ready     <= '0;
      
    endfunction

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge tl_bus.clk_i);
    endtask

    task perform_transfer(input tl_h2d_t tl_req); 
      while (!lock.try_get()) begin
        cycle_end();
      end
       
      tl_bus.tl_req.a_address   <= #TA tl_req.a_address;
      tl_bus.tl_req.a_opcode    <= #TA tl_req.a_opcode;
      tl_bus.tl_req.a_size      <= #TA tl_req.a_size;
      tl_bus.tl_req.a_source    <= #TA tl_req.a_source;
      tl_bus.tl_req.a_mask      <= #TA tl_req.a_mask;
      tl_bus.tl_req.a_data      <= #TA tl_req.a_data;
      tl_bus.tl_req.a_valid     <= #TA 1'b1;
          
      @(posedge tl_bus.tl_rsp.d_valid)
        
      if(tl_bus.tl_req.a_opcode == tlul_ot_pkg::Get)
        $display("Read:  %0h at Addr: %0h", tl_bus.tl_rsp.d_data, tl_bus.tl_req.a_address);
      else 
        $display("Wrote: %0h at Addr: %0h", tl_bus.tl_req.a_data, tl_bus.tl_req.a_address);
    
      tl_bus.tl_req.a_valid     <= #TA 1'b0;
      tl_bus.tl_req.d_ready     <= #TA 1'b1;
      tl_bus.tl_req.a_data      <= #TA 32'b0;
       
     
      cycle_end();
      
      reset_master();
       
      lock.put();
         
    endtask 
     
    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) cycle_end();
    endtask 
     
    // set random opcode (not all the comb of 3 bit are allowed)
    function tlul_ot_pkg::tl_a_op_e new_rand_opcode();
      automatic tlul_ot_pkg::tl_a_op_e opcode;
      int index;
      index = $urandom_range(0,2);
      case(index)
        3'd0:    opcode = tlul_ot_pkg::PutFullData;
        3'd1:    opcode = tlul_ot_pkg::PutPartialData;
        3'd2:    opcode = tlul_ot_pkg::Get; 
        default: opcode = tlul_ot_pkg::Get;
      endcase
      return opcode; 
    endfunction 

    // set random address into a certain [min,max] range
    function logic [31:0] new_rand_addr(input logic [31:0] in_addr, input logic [31:0] end_addr);
      logic [31:0] rand_addr;
      logic rand_success; 
      rand_success = std::randomize(rand_addr) with { rand_addr >= in_addr; rand_addr <= end_addr;}; 
      assert(rand_success);
      return rand_addr;     
    endfunction

    // set random mask if PutPartialData or fix it to '1 otherwise
    function logic [3:0] new_rand_mask(input tlul_ot_pkg::tl_a_op_e opcode);
      logic [3:0] rand_mask;
      logic rand_success;
      if(opcode == tlul_ot_pkg::PutPartialData) begin
         rand_success = std::randomize(rand_mask); 
         assert(rand_success);
      end else
         rand_mask = 4'b1;
      return rand_mask;
    endfunction
     
    // set the size according to the mask configuration
    function logic [1:0] new_size(input logic [3:0] mask);
      logic [1:0] size = 0;     
      for(int i=0;i<3;i++)
         if(mask[i])
           size++;
      return size;
    endfunction 
   
    // set random write data
    function logic [31:0] new_rand_data(input tlul_ot_pkg::tl_a_op_e opcode);
      logic [31:0] data;
      logic rand_success;
      if(opcode != tlul_ot_pkg::Get) begin
        rand_success = std::randomize(data); 
        assert(rand_success);
      end else
        data = 32'b0;  
      return data;
    endfunction
     
    // set random source
    function logic [7:0] new_rand_source();
      logic [31:0] source;
      logic rand_success;
      rand_success = std::randomize(source); 
      assert(rand_success);
      return source;
    endfunction

    task run (input int unsigned min_wait, input int unsigned max_wait);
      tlul_ot_pkg::tl_h2d_t tl_req;
      logic [31:0] in_addr  = 32'h1A000000;
      logic [31:0] end_addr = 32'h1A11FFFF;
       
      tl_req.a_opcode  = new_rand_opcode(                   );
      tl_req.a_address = new_rand_addr  ( in_addr, end_addr );
      tl_req.a_mask    = new_rand_mask  ( tl_req.a_opcode   );
      tl_req.a_size    = new_size       ( tl_req.a_mask     );
      tl_req.a_data    = new_rand_data  ( tl_req.a_opcode   );
      tl_req.a_source  = new_rand_source(                   );
       
      perform_transfer(tl_req);
      rand_wait(min_wait, max_wait);
      reset_master(); 
    endtask
 
  endclass 

endpackage
