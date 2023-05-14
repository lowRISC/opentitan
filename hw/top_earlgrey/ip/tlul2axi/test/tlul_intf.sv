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

interface tlul_bus;
   import tlul_ot_pkg::*;
   logic clk_i;
   tl_h2d_t tl_req;
   tl_d2h_t tl_rsp;

   modport HOST(           
    output tl_req,
    input  tl_rsp            
   );
   modport DEVICE(
    input  tl_req,            
    output tl_rsp  
   );
   
endinterface
