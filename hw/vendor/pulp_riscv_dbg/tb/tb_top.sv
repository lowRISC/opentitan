// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Top level wrapper for a RI5CY testbench
// Contributor: Robert Balas <balasr@iis.ee.ethz.ch>
//              Jeremy Bennett <jeremy.bennett@embecosm.com>

module tb_top #(
    parameter int unsigned INSTR_RDATA_WIDTH = 32,
    parameter int unsigned RAM_ADDR_WIDTH = 22,
    parameter logic [31:0] BOOT_ADDR  = 'h1A00_0180,
    parameter bit          JTAG_BOOT  = 1,
    parameter int unsigned OPENOCD_PORT = 9999
);

    // comment to record execution trace
    //`define TRACE_EXECUTION

    const time CLK_PHASE_HI         = 5ns;
    const time CLK_PHASE_LO         = 5ns;
    const time CLK_PERIOD           = CLK_PHASE_HI + CLK_PHASE_LO;
    const time STIM_APPLICATION_DEL = CLK_PERIOD * 0.1;
    const time RESP_ACQUISITION_DEL = CLK_PERIOD * 0.9;
    const time RESET_DEL            = STIM_APPLICATION_DEL;
    const int  RESET_WAIT_CYCLES    = 4;

    // clock and reset for tb
    logic                   clk     = 'b1;
    logic                   rst_n   = 'b0;

    // testbench result
    logic                   tests_passed;
    logic                   tests_failed;

   // signals for ri5cy
    logic                   fetch_enable;


    // make the core start fetching instruction immediately
    assign fetch_enable = '1;

    // allow vcd dump
    initial begin: dump_vars
        if ($test$plusargs("vcd")) begin
            $dumpfile("riscy_tb.vcd");
            $dumpvars(0, tb_top);
        end
`ifdef QUESTA
        if ($test$plusargs("wlfdump")) begin
            $wlfdumpvars(0, tb_top);
        end
`endif
    end

    // we either load the provided firmware or execute a small test program that
    // doesn't do more than an infinite loop with some I/O
    initial begin: load_prog
        automatic logic [1023:0] firmware;
        automatic int prog_size = 6;

        if($value$plusargs("firmware=%s", firmware)) begin
            if($test$plusargs("verbose"))
                $display("[TESTBENCH] %t: loading firmware %0s ...",
                         $time, firmware);
            $readmemh(firmware, tb_test_env_i.mm_ram_i.dp_ram_i.mem);

        end else begin
            $display("No firmware specified");
        end
    end

    // clock generation
    initial begin: clock_gen
        forever begin
            #CLK_PHASE_HI clk = 1'b0;
            #CLK_PHASE_LO clk = 1'b1;
        end
    end: clock_gen

    // reset generation
    initial begin: reset_gen
        rst_n          = 1'b0;

        // wait a few cycles
        repeat (RESET_WAIT_CYCLES) begin
            @(posedge clk); //TODO: was posedge, see below
        end

        // start running
        #RESET_DEL rst_n = 1'b1;
        if($test$plusargs("verbose"))
            $display("reset deasserted", $time);

    end: reset_gen

    // set timing format
    initial begin: timing_format
        $timeformat(-9, 0, "ns", 9);
    end: timing_format

    // check if we succeded
    always_ff @(posedge clk, negedge rst_n) begin
        if (tests_passed) begin
            $display("Exit Success");
            $finish;
        end
        if (tests_failed) begin
            $display("Exit FAILURE");
            $finish;
        end
    end

    // wrapper for riscv, the memory system and stdout peripheral
    tb_test_env #(
        .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH),
        .RAM_ADDR_WIDTH (RAM_ADDR_WIDTH),
        .BOOT_ADDR (BOOT_ADDR),
        .PULP_SECURE (1),
        .JTAG_BOOT (JTAG_BOOT),
        .OPENOCD_PORT (OPENOCD_PORT)
    ) tb_test_env_i(
        .clk_i          ( clk            ),
        .rst_ni         ( rst_n          ),
        .fetch_enable_i ( fetch_enable   ),
        .tests_passed_o ( tests_passed   ),
        .tests_failed_o ( tests_failed   )
    );

endmodule // tb_top
