// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Contributor: Robert Balas <balasr@iis.ethz.ch>


package dm_tb_pkg;

    // PULPissimo-like memory map
    typedef enum logic [31:0] {
        ROM_BASE      = 32'h1A00_0000,
        FLL_BASE      = 32'h1A10_0000,
        GPIO_BASE     = 32'h1A10_1000,
        UDMA_BASE     = 32'h1A10_2000,
        CNTRL_BASE    = 32'h1A10_4000,
        ADVTIMER_BASE = 32'h1A10_5000,
        EVENT_BASE    = 32'h1A10_6000,
        TIMER_BASE    = 32'h1A10_B000,
        HWPE_BASE     = 32'h1A10_C000,
        STDOUT_BASE   = 32'h1A10_F000,
        DEBUG_BASE    = 32'h1A11_0000,
        SRAM_BASE     = 32'h1C00_0000
   } mmap_base_t;

    localparam logic [31:0] ROM_LEN      = 32'h0010_0000;
    localparam logic [31:0] FLL_LEN      = 32'h0000_1000;
    localparam logic [31:0] GPIO_LEN     = 32'h0000_1000;
    localparam logic [31:0] UDMA_LEN     = 32'h0000_2000;
    localparam logic [31:0] CNTRL_LEN    = 32'h0000_1000;
    localparam logic [31:0] ADVTIMER_LEN = 32'h0000_1000;
    localparam logic [31:0] EVENT_LEN    = 32'h0000_5000;
    localparam logic [31:0] TIMER_LEN    = 32'h0000_1000;
    localparam logic [31:0] HWPE_LEN     = 32'h0000_3000;
    localparam logic [31:0] STDOUT_LEN   = 32'h0000_1000;
    localparam logic [31:0] DEBUG_LEN    = 32'h0000_1000;
    localparam logic [31:0] SRAM_LEN     = 32'h000f_C000;

    // helper functions
    function automatic logic [31:0] jal (logic[4:0] rd, logic [20:0] imm);
        return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h6f};
    endfunction

    function automatic logic [31:0] jalr (logic[4:0] rd, logic[4:0] rs1, logic [11:0] offset);
        return {offset[11:0], rs1, 3'b0, rd, 7'h67};
    endfunction

    function automatic logic [31:0] lui (logic[4:0] rd, logic [19:0] uimm);
        return {uimm, rd, 7'b0110111};
    endfunction

endpackage // riscv_tb_pkg
