// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for a RI5CY testbench, containing RI5CY, Memory and stdout peripheral
// Contributor: Robert Balas <balasr@iis.ee.ethz.ch>

module tb_test_env #(
    parameter int unsigned INSTR_RDATA_WIDTH = 32,
    parameter int unsigned RAM_ADDR_WIDTH = 20,
    parameter logic [31:0] BOOT_ADDR = 'h80,
    parameter bit          PULP_SECURE = 1,
    parameter bit          JTAG_BOOT = 1,
    parameter int unsigned OPENOCD_PORT = 0,
    parameter bit          A_EXTENSION = 0
) (
    input logic  clk_i,
    input logic  rst_ni,

    // currently we are not making use of those signals
    input logic  fetch_enable_i,
    output logic tests_passed_o,
    output logic tests_failed_o);

    // defs from pulpissimo
    // localparam CLUSTER_ID         = 6'd31;
    // localparam CORE_ID            = 4'd0;
    // test defs
    localparam CLUSTER_ID         = 6'd0;
    localparam CORE_ID            = 4'd0;

    localparam CORE_MHARTID       = {CLUSTER_ID, 1'b0, CORE_ID};
    localparam NrHarts                               = 1;
    localparam logic [NrHarts-1:0] SELECTABLE_HARTS  = 1 << CORE_MHARTID;

    // signals connecting core to memory
    logic                        instr_req;
    logic                        instr_gnt;
    logic                        instr_rvalid;
    logic [31:0]                 instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                        data_req;
    logic                        data_gnt;
    logic                        data_rvalid;
    logic [31:0]                 data_addr;
    logic                        data_we;
    logic [3:0]                  data_be;
    logic [31:0]                 data_rdata;
    logic [31:0]                 data_wdata;

    // jtag openocd bridge signals
    logic                        sim_jtag_tck;
    logic                        sim_jtag_tms;
    logic                        sim_jtag_tdi;
    logic                        sim_jtag_trstn;
    logic                        sim_jtag_tdo;
    logic [31:0]                 sim_jtag_exit;
    logic                        sim_jtag_enable;

    // signals for debug unit
    logic                        debug_req_ready;
    dm::dmi_resp_t               debug_resp;
    logic                        jtag_req_valid;
    dm::dmi_req_t                jtag_dmi_req;
    logic                        jtag_resp_ready;
    logic                        jtag_resp_valid;
    logic [NrHarts-1:0]          dm_debug_req;
    logic                        ndmreset, ndmreset_n;

    // debug unit slave interface
    logic                        dm_grant;
    logic                        dm_rvalid;
    logic                        dm_req;
    logic                        dm_we;
    logic [31:0]                 dm_addr;
    logic [31:0]                 dm_wdata;
    logic [31:0]                 dm_rdata;
    logic [3:0]                  dm_be;

    // debug unit master interface (system bus access)
    logic                        sb_req;
    logic [31:0]                 sb_addr;
    logic                        sb_we;
    logic [31:0]                 sb_wdata;
    logic [3:0]                  sb_be;
    logic                        sb_gnt;
    logic                        sb_rvalid;
    logic [31:0]                 sb_rdata;

    // irq signals (not used)
    logic                        irq;
    logic [0:4]                  irq_id_in;
    logic                        irq_ack;
    logic [0:4]                  irq_id_out;
    logic                        irq_sec;

    // make jtag bridge work
    assign sim_jtag_enable = JTAG_BOOT;

    // interrupts (only timer for now)
    assign irq_sec = '0;

    // instantiate the core
    riscv_core #(
        .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH),
        .PULP_SECURE(PULP_SECURE),
        .A_EXTENSION(A_EXTENSION),
        .FPU(0)
    ) riscv_core_i (
        .clk_i                  ( clk_i                 ),
        .rst_ni                 ( ndmreset_n            ),

        .clock_en_i             ( '1                    ),
        .test_en_i              ( '0                    ),

        .boot_addr_i            ( BOOT_ADDR             ),
        .core_id_i              ( CORE_ID               ),
        .cluster_id_i           ( CLUSTER_ID            ),

        .instr_addr_o           ( instr_addr            ),
        .instr_req_o            ( instr_req             ),
        .instr_rdata_i          ( instr_rdata           ),
        .instr_gnt_i            ( instr_gnt             ),
        .instr_rvalid_i         ( instr_rvalid          ),

        .data_addr_o            ( data_addr             ),
        .data_wdata_o           ( data_wdata            ),
        .data_we_o              ( data_we               ),
        .data_req_o             ( data_req              ),
        .data_be_o              ( data_be               ),
        .data_rdata_i           ( data_rdata            ),
        .data_gnt_i             ( data_gnt              ),
        .data_rvalid_i          ( data_rvalid           ),
        .data_atop_o            (                       ),

        .apu_master_req_o       (                       ),
        .apu_master_ready_o     (                       ),
        .apu_master_gnt_i       (                       ),
        .apu_master_operands_o  (                       ),
        .apu_master_op_o        (                       ),
        .apu_master_type_o      (                       ),
        .apu_master_flags_o     (                       ),
        .apu_master_valid_i     (                       ),
        .apu_master_result_i    (                       ),
        .apu_master_flags_i     (                       ),


        .irq_software_i         ( 1'b0                  ),
        .irq_timer_i            ( 1'b0                  ),
        .irq_external_i         ( 1'b0                  ),
        .irq_fast_i             ( 15'b0                 ),
        .irq_nmi_i              ( 1'b0                  ),
        .irq_fastx_i            ( 32'b0                 ),

        .irq_ack_o              ( irq_ack               ),
        .irq_id_o               ( irq_id_out            ),
        .irq_sec_i              ( irq_sec               ),

        .sec_lvl_o              ( sec_lvl_o             ),

        .debug_req_i            ( dm_debug_req[CORE_MHARTID] ),

        .fetch_enable_i         ( fetch_enable_i        ),
        .core_busy_o            ( core_busy_o           ),

        .ext_perf_counters_i    (                       ),
        .fregfile_disable_i     ( 1'b0                  )
    );

    // this handles read to RAM and memory mapped pseudo peripherals
    mm_ram #(
        .RAM_ADDR_WIDTH (RAM_ADDR_WIDTH),
        .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH),
        .JTAG_BOOT(JTAG_BOOT)
    ) mm_ram_i (
        .clk_i          ( clk_i           ),
        .rst_ni         ( ndmreset_n      ),

        // core instruction access
        .instr_req_i    ( instr_req       ),
        .instr_addr_i   ( instr_addr      ),
        .instr_rdata_o  ( instr_rdata     ),
        .instr_rvalid_o ( instr_rvalid    ),
        .instr_gnt_o    ( instr_gnt       ),

        // core data access
        .data_req_i     ( data_req        ),
        .data_addr_i    ( data_addr       ),
        .data_we_i      ( data_we         ),
        .data_be_i      ( data_be         ),
        .data_wdata_i   ( data_wdata      ),
        .data_rdata_o   ( data_rdata      ),
        .data_rvalid_o  ( data_rvalid     ),
        .data_gnt_o     ( data_gnt        ),

        // system bus access from debug unit
        .sb_req_i       ( sb_req          ),
        .sb_addr_i      ( sb_addr         ),
        .sb_we_i        ( sb_we           ),
        .sb_be_i        ( sb_be           ),
        .sb_wdata_i     ( sb_wdata        ),
        .sb_rdata_o     ( sb_rdata        ),
        .sb_rvalid_o    ( sb_rvalid       ),
        .sb_gnt_o       ( sb_gnt          ),

        // access to debug unit
        .dm_req_o       ( dm_req          ),
        .dm_addr_o      ( dm_addr         ),
        .dm_we_o        ( dm_we           ),
        .dm_be_o        ( dm_be           ),
        .dm_wdata_o     ( dm_wdata        ),
        .dm_rdata_i     ( dm_rdata        ),
        .dm_rvalid_i    ( dm_rvalid       ),
        .dm_gnt_i       ( dm_gnt          ),


        .irq_id_i       ( irq_id_out      ),
        .irq_ack_i      ( irq_ack         ),
        .irq_id_o       ( irq_id_in       ),
        .irq_o          ( irq             ),

        .tests_passed_o ( tests_passed_o  ),
        .tests_failed_o ( tests_failed_o  )
    );

    // debug subsystem
    dmi_jtag #(
        .IdcodeValue          ( 32'h249511C3    )
    ) i_dmi_jtag (
        .clk_i                ( clk_i           ),
        .rst_ni               ( rst_ni          ),
        .testmode_i           ( 1'b0            ),
        .dmi_req_o            ( jtag_dmi_req    ),
        .dmi_req_valid_o      ( jtag_req_valid  ),
        .dmi_req_ready_i      ( debug_req_ready ),
        .dmi_resp_i           ( debug_resp      ),
        .dmi_resp_ready_o     ( jtag_resp_ready ),
        .dmi_resp_valid_i     ( jtag_resp_valid ),
        .dmi_rst_no           (                 ), // not connected
        .tck_i                ( sim_jtag_tck    ),
        .tms_i                ( sim_jtag_tms    ),
        .trst_ni              ( sim_jtag_trstn  ),
        .td_i                 ( sim_jtag_tdi    ),
        .td_o                 ( sim_jtag_tdo    ),
        .tdo_oe_o             (                 )
    );

    dm_top #(
       .NrHarts           ( NrHarts           ),
       .BusWidth          ( 32                ),
       .SelectableHarts   ( SELECTABLE_HARTS  )
    ) i_dm_top (

       .clk_i             ( clk_i             ),
       .rst_ni            ( rst_ni            ),
       .testmode_i        ( 1'b0              ),
       .ndmreset_o        ( ndmreset          ),
       .dmactive_o        (                   ), // active debug session TODO
       .debug_req_o       ( dm_debug_req      ),
       .unavailable_i     ( ~SELECTABLE_HARTS ),
       .hartinfo_i        ( '0                ),

       .slave_req_i       ( dm_req            ),
       .slave_we_i        ( dm_we             ),
       .slave_addr_i      ( dm_addr           ),
       .slave_be_i        ( dm_be             ),
       .slave_wdata_i     ( dm_wdata          ),
       .slave_rdata_o     ( dm_rdata          ),

       .master_req_o      ( sb_req            ),
       .master_add_o      ( sb_addr           ),
       .master_we_o       ( sb_we             ),
       .master_wdata_o    ( sb_wdata          ),
       .master_be_o       ( sb_be             ),
       .master_gnt_i      ( sb_gnt            ),
       .master_r_valid_i  ( sb_rvalid         ),
       .master_r_rdata_i  ( sb_rdata          ),

       .dmi_rst_ni        ( rst_ni            ),
       .dmi_req_valid_i   ( jtag_req_valid    ),
       .dmi_req_ready_o   ( debug_req_ready   ),
       .dmi_req_i         ( jtag_dmi_req      ),
       .dmi_resp_valid_o  ( jtag_resp_valid   ),
       .dmi_resp_ready_i  ( jtag_resp_ready   ),
       .dmi_resp_o        ( debug_resp        )
    );

    // grant in the same cycle
    assign dm_gnt = dm_req;
    // valid read/write in the next cycle
    always_ff @(posedge clk_i or negedge rst_ni) begin : dm_valid_handler
        if(~rst_ni) begin
            dm_rvalid <= '0;
        end else begin
            dm_rvalid <= dm_gnt;
        end
    end

    // reset handling with ndmreset
    rstgen i_rstgen_main (
        .clk_i        ( clk_i                ),
        .rst_ni       ( rst_ni & (~ndmreset) ),
        .test_mode_i  ( '0                   ),
        .rst_no       ( ndmreset_n           ),
        .init_no      (                      ) // keep open
    );

    // jtag calls from dpi
    SimJTAG #(
        .TICK_DELAY (1),
        .PORT(OPENOCD_PORT)
    ) i_sim_jtag (
        .clock                ( clk_i                ),
        .reset                ( ~rst_ni              ),
        .enable               ( sim_jtag_enable      ),
        .init_done            ( rst_ni               ),
        .jtag_TCK             ( sim_jtag_tck         ),
        .jtag_TMS             ( sim_jtag_tms         ),
        .jtag_TDI             ( sim_jtag_tdi         ),
        .jtag_TRSTn           ( sim_jtag_trstn       ),
        .jtag_TDO_data        ( sim_jtag_tdo         ),
        .jtag_TDO_driven      ( 1'b1                 ),
        .exit                 ( sim_jtag_exit        )
    );

    always_comb begin : jtag_exit_handler
        if (sim_jtag_exit)
            $finish(2); // print stats too
    end

endmodule // tb_test_env
