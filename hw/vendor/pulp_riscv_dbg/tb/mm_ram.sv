// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// RAM and MM wrapper for RI5CY
// Contributor: Robert Balas <balasr@iis.ee.ethz.ch>
//
// This maps the dp_ram module to the instruction and data ports of the RI5CY
// processor core and some pseudo peripherals

module mm_ram #(
    parameter int unsigned RAM_ADDR_WIDTH = 16,
    parameter int unsigned INSTR_RDATA_WIDTH = 32,
    parameter bit          JTAG_BOOT = 1
) (
    input logic                          clk_i,
    input logic                          rst_ni,

    input logic                          instr_req_i,
    input logic [31:0]                   instr_addr_i,
    output logic [INSTR_RDATA_WIDTH-1:0] instr_rdata_o,
    output logic                         instr_rvalid_o,
    output logic                         instr_gnt_o,

    input logic                          data_req_i,
    input logic [31:0]                   data_addr_i,
    input logic                          data_we_i,
    input logic [3:0]                    data_be_i,
    input logic [31:0]                   data_wdata_i,
    output logic [31:0]                  data_rdata_o,
    output logic                         data_rvalid_o,
    output logic                         data_gnt_o,

    input logic                          sb_req_i,
    input logic [31:0]                   sb_addr_i,
    input logic                          sb_we_i,
    input logic [3:0]                    sb_be_i,
    input logic [31:0]                   sb_wdata_i,
    output logic [31:0]                  sb_rdata_o,
    output logic                         sb_rvalid_o,
    output logic                         sb_gnt_o,

    output logic                         dm_req_o,
    output logic [31:0]                  dm_addr_o,
    output logic                         dm_we_o,
    output logic [3:0]                   dm_be_o,
    output logic [31:0]                  dm_wdata_o,
    input logic [31:0]                   dm_rdata_i,
    input logic                          dm_rvalid_i,
    input logic                          dm_gnt_i,


    input logic [4:0]                    irq_id_i,
    input logic                          irq_ack_i,
    output logic [4:0]                   irq_id_o,
    output logic                         irq_o,

    output logic                         tests_passed_o,
    output logic                         tests_failed_o
);

    import dm_tb_pkg::*;

    localparam int                    TIMER_IRQ_ID = 3;

    // mux for read and writes
    enum logic [2:0]{RAM, DEBUG, ROM, UNMAP, IDLE_READ} select_rdata_d, select_rdata_q;

    enum logic [1:0]{SB, CORE, IDLE_WRITE} select_wdata_d, select_wdata_q;

    logic                          data_rvalid_d, data_rvalid_q;
    logic                          sb_rvalid_d, sb_rvalid_q;
    logic                          instr_rvalid_d, instr_rvalid_q;

    // TODO: oof
    logic [31:0]                   data_addr_aligned;

    // signals to ram
    logic                          ram_data_req;
    logic [RAM_ADDR_WIDTH-1:0]     ram_data_addr;
    logic [31:0]                   ram_data_wdata;
    logic [31:0]                   ram_data_rdata;
    logic                          ram_data_we;
    logic [3:0]                    ram_data_be;

    // signals to rom
    logic                          rom_req;
    logic [31:0]                   rom_addr;
    logic [31:0]                   rom_rdata;

    // signals to read access debug unit
    logic                          dm_req;
    logic [31:0]                   dm_addr;
    logic                          dm_we;
    logic [3:0]                    dm_be;
    logic [31:0]                   dm_wdata;
    logic [31:0]                   dm_rdata;
    logic                          dm_rvalid;
    logic                          dm_gnt;

    logic                          ram_instr_req;
    logic [31:0]                   ram_instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0]  ram_instr_rdata;




    // signals to print peripheral
    logic [31:0]                   print_wdata;
    logic                          print_valid;

    // signals to timer
    logic [31:0]                   timer_irq_mask_q;
    logic [31:0]                   timer_cnt_q;
    logic                          irq_q;
    logic                          timer_reg_valid;
    logic                          timer_val_valid;
    logic [31:0]                   timer_wdata;


    // uhh, align?
    always_comb data_addr_aligned = {data_addr_i[31:2], 2'b0};

    // Handle system bus, core data accesses and instr access to rom, ram and
    // debug unit. Someone make a for gen loop here.
    always_comb begin
        sb_gnt_o       = '0;
        data_gnt_o     = '0;
        instr_gnt_o    = '0;

        ram_data_req   = '0;
        ram_data_addr  = '0;
        ram_data_wdata = '0;
        ram_data_we    = '0;
        ram_data_be    = '0;

        ram_instr_req  = '0;
        ram_instr_addr = '0;

        dm_req         = '0;
        dm_addr        = '0;
        dm_we          = '0;
        dm_be          = '0;
        dm_wdata       = '0;

        rom_req        = '0;
        rom_addr       = '0;

        print_wdata    = '0;
        print_valid    = '0;

        select_rdata_d = IDLE_READ;
        select_wdata_d = IDLE_WRITE;

        data_rvalid_d  = '0;
        sb_rvalid_d    = '0;
        instr_rvalid_d = '0;

        tests_passed_o = '0;
        tests_failed_o = '0;


        // memory map:
        // the ram is mapped from 0 to SRAM_LEN and SRAM_BASE to SRAM_BASE + SRAM_LEN
        // this mirroring is the same as in pulpissimo

        // instruction data reads to ram can always go
        if (instr_req_i && ((instr_addr_i >= SRAM_BASE && instr_addr_i < SRAM_BASE + SRAM_LEN) ||
                             (instr_addr_i >= 0 && instr_addr_i < SRAM_LEN))) begin
            instr_gnt_o    = '1;
            instr_rvalid_d = '1;
            ram_instr_req  = '1;
            ram_instr_addr = instr_addr_i;

        end


        // priority to sb access over data access
        if (sb_req_i) begin
            sb_gnt_o = '1;
            sb_rvalid_d  = '1;

            if (sb_we_i) begin // handle writes
                if (sb_addr_i >= ROM_BASE && sb_addr_i < ROM_BASE + ROM_LEN) begin
                end else if (sb_addr_i >= FLL_BASE && sb_addr_i < FLL_BASE + FLL_LEN) begin
                end else if (sb_addr_i >= GPIO_BASE && sb_addr_i < GPIO_BASE + GPIO_LEN) begin
                end else if (sb_addr_i >= UDMA_BASE && sb_addr_i < UDMA_BASE + UDMA_LEN) begin
                end else if (sb_addr_i >= CNTRL_BASE && sb_addr_i < CNTRL_BASE + CNTRL_LEN) begin
                end else if (sb_addr_i >= ADVTIMER_BASE && sb_addr_i < ADVTIMER_BASE + ADVTIMER_LEN) begin
                end else if (sb_addr_i >= EVENT_BASE && sb_addr_i < EVENT_BASE + EVENT_LEN) begin
                end else if (sb_addr_i >= TIMER_BASE && sb_addr_i < TIMER_BASE + TIMER_LEN) begin
                end else if (sb_addr_i >= HWPE_BASE && sb_addr_i < HWPE_BASE + HWPE_LEN) begin
                end else if (sb_addr_i >= STDOUT_BASE && sb_addr_i < STDOUT_BASE + STDOUT_LEN) begin
                    select_wdata_d  = SB;
                    print_wdata = sb_wdata_i;
                    print_valid = '1;

                end else if (sb_addr_i >= DEBUG_BASE && sb_addr_i < DEBUG_BASE + DEBUG_LEN) begin
                end else if ((sb_addr_i >= SRAM_BASE && sb_addr_i < SRAM_BASE + SRAM_LEN) ||
                                           (sb_addr_i >= 0 && sb_addr_i < SRAM_LEN)) begin
                    select_wdata_d  = SB;
                    ram_data_req = sb_req_i;
                    ram_data_addr = sb_addr_i[RAM_ADDR_WIDTH-1:0]; // just clip higher bits
                    ram_data_wdata = sb_wdata_i;
                    ram_data_we = sb_we_i;
                    ram_data_be = sb_be_i;

                end else begin
                    $error("Writing to unmapped memory at %x", sb_addr_i);
                end

            end else begin // handle reads
                if (sb_addr_i >= ROM_BASE && sb_addr_i < ROM_BASE + ROM_LEN) begin
                    select_rdata_d = ROM;

                end else if (sb_addr_i >= FLL_BASE && sb_addr_i < FLL_BASE + FLL_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= GPIO_BASE && sb_addr_i < GPIO_BASE + GPIO_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= UDMA_BASE && sb_addr_i < UDMA_BASE + UDMA_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= CNTRL_BASE && sb_addr_i < CNTRL_BASE + CNTRL_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= ADVTIMER_BASE && sb_addr_i < ADVTIMER_BASE + ADVTIMER_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= EVENT_BASE && sb_addr_i < EVENT_BASE + EVENT_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= TIMER_BASE && sb_addr_i < TIMER_BASE + TIMER_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= HWPE_BASE && sb_addr_i < HWPE_BASE + HWPE_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= STDOUT_BASE && sb_addr_i < STDOUT_BASE + STDOUT_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (sb_addr_i >= DEBUG_BASE && sb_addr_i < DEBUG_BASE + DEBUG_LEN) begin
                    select_rdata_d = UNMAP;
                end else if ((sb_addr_i >= SRAM_BASE && sb_addr_i < SRAM_BASE + SRAM_LEN) ||
                                           (sb_addr_i >= 0 && sb_addr_i < SRAM_LEN)) begin
                    select_rdata_d = RAM;
                    ram_data_req = sb_req_i;
                    ram_data_addr = sb_addr_i[RAM_ADDR_WIDTH-1:0];
                    ram_data_wdata = sb_wdata_i;
                    ram_data_we = sb_we_i;
                    ram_data_be = sb_be_i;

                end else begin
                    select_rdata_d = UNMAP;
                end

            end
        end else if (data_req_i) begin
            data_gnt_o = '1;
            data_rvalid_d  = '1;

            if (data_we_i) begin // handle writes
                if (data_addr_i >= ROM_BASE && data_addr_i < ROM_BASE + ROM_LEN) begin
                end else if (data_addr_i >= FLL_BASE && data_addr_i < FLL_BASE + FLL_LEN) begin
                end else if (data_addr_i >= GPIO_BASE && data_addr_i < GPIO_BASE + GPIO_LEN) begin
                end else if (data_addr_i >= UDMA_BASE && data_addr_i < UDMA_BASE + UDMA_LEN) begin
                end else if (data_addr_i >= CNTRL_BASE && data_addr_i < CNTRL_BASE + CNTRL_LEN) begin
                    if(data_wdata_i === 32'hF00D)
                        tests_passed_o = 1'b1;
                    else
                        tests_failed_o = 1'b1;

                end else if (data_addr_i >= ADVTIMER_BASE && data_addr_i < ADVTIMER_BASE + ADVTIMER_LEN) begin
                end else if (data_addr_i >= EVENT_BASE && data_addr_i < EVENT_BASE + EVENT_LEN) begin
                end else if (data_addr_i >= TIMER_BASE && data_addr_i < TIMER_BASE + TIMER_LEN) begin
                end else if (data_addr_i >= HWPE_BASE && data_addr_i < HWPE_BASE + HWPE_LEN) begin
                end else if (data_addr_i >= STDOUT_BASE && data_addr_i < STDOUT_BASE + STDOUT_LEN) begin
                    select_wdata_d  = CORE;
                    print_wdata = data_wdata_i;
                    print_valid = '1;

                end else if (data_addr_i >= DEBUG_BASE && data_addr_i < DEBUG_BASE + DEBUG_LEN) begin
                    select_wdata_d  = CORE;
                    dm_req    = data_req_i;
                    dm_addr   = data_addr_i;
                    dm_we     = data_we_i;
                    dm_be     = data_be_i;
                    dm_wdata  = data_wdata_i;

                end else if ((data_addr_i >= SRAM_BASE && data_addr_i < SRAM_BASE + SRAM_LEN) ||
                                             (data_addr_i >= 0 && data_addr_i < SRAM_LEN)) begin
                    select_wdata_d  = CORE;
                    ram_data_req = data_req_i;
                    ram_data_addr = data_addr_i[RAM_ADDR_WIDTH-1:0]; // just clip higher bits
                    ram_data_wdata = data_wdata_i;
                    ram_data_we = data_we_i;
                    ram_data_be = data_be_i;

                end else begin
                end

            end else begin // handle reads
                if (data_addr_i >= ROM_BASE && data_addr_i < ROM_BASE + ROM_LEN) begin
                    select_rdata_d = ROM;
                    rom_req  = data_req_i;
                    rom_addr = data_addr_i - ROM_BASE;
                    // TODO data_be_i

                end else if (data_addr_i >= FLL_BASE && data_addr_i < FLL_BASE + FLL_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= GPIO_BASE && data_addr_i < GPIO_BASE + GPIO_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= UDMA_BASE && data_addr_i < UDMA_BASE + UDMA_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= CNTRL_BASE && data_addr_i < CNTRL_BASE + CNTRL_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= ADVTIMER_BASE && data_addr_i < ADVTIMER_BASE + ADVTIMER_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= EVENT_BASE && data_addr_i < EVENT_BASE + EVENT_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= TIMER_BASE && data_addr_i < TIMER_BASE + TIMER_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= HWPE_BASE && data_addr_i < HWPE_BASE + HWPE_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= STDOUT_BASE && data_addr_i < STDOUT_BASE + STDOUT_LEN) begin
                    select_rdata_d = UNMAP;
                end else if (data_addr_i >= DEBUG_BASE && data_addr_i < DEBUG_BASE + DEBUG_LEN) begin
                    select_rdata_d = DEBUG;
                    dm_req    = data_req_i;
                    dm_addr   = data_addr_i;
                    dm_we     = data_we_i;
                    dm_be     = data_be_i;

                end else if ((data_addr_i >= SRAM_BASE && data_addr_i < SRAM_BASE + SRAM_LEN) ||
                                             (data_addr_i >= 0 && data_addr_i < SRAM_LEN)) begin
                    select_rdata_d = RAM;
                    ram_data_req = data_req_i;
                    ram_data_addr = data_addr_i[RAM_ADDR_WIDTH-1:0];
                    ram_data_we = data_we_i;
                    ram_data_be = data_be_i;

                end else begin
                    select_rdata_d = UNMAP;
                end

            end
        end else if (instr_req_i) begin
            instr_gnt_o = '1;
            instr_rvalid_d  = '1;
            // handle reads
            if (instr_addr_i >= ROM_BASE && instr_addr_i < ROM_BASE + ROM_LEN) begin
                select_rdata_d = ROM;
                rom_req  = instr_req_i;
                rom_addr = instr_addr_i - ROM_BASE - 32'h80;

            end else if (instr_addr_i >= FLL_BASE && instr_addr_i < FLL_BASE + FLL_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= GPIO_BASE && instr_addr_i < GPIO_BASE + GPIO_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= UDMA_BASE && instr_addr_i < UDMA_BASE + UDMA_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= CNTRL_BASE && instr_addr_i < CNTRL_BASE + CNTRL_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= ADVTIMER_BASE && instr_addr_i < ADVTIMER_BASE + ADVTIMER_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= EVENT_BASE && instr_addr_i < EVENT_BASE + EVENT_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= TIMER_BASE && instr_addr_i < TIMER_BASE + TIMER_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= HWPE_BASE && instr_addr_i < HWPE_BASE + HWPE_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= STDOUT_BASE && instr_addr_i < STDOUT_BASE + STDOUT_LEN) begin
                select_rdata_d = UNMAP;
            end else if (instr_addr_i >= DEBUG_BASE && instr_addr_i < DEBUG_BASE + DEBUG_LEN) begin
                select_rdata_d = DEBUG;
                dm_req    = '1;
                dm_addr   = instr_addr_i;
                dm_we     = '0;
                dm_be     = 4'b1111;

            end else if ((instr_addr_i >= SRAM_BASE && instr_addr_i < SRAM_BASE + SRAM_LEN) ||
                                          (instr_addr_i >=0 && instr_addr_i < SRAM_LEN)) begin
                // handled separately
                select_rdata_d = RAM;
            end else begin
                select_rdata_d = UNMAP;
            end
        end
    end


`ifndef VERILATOR
    // make sure we don't access any unmapped memory

    out_of_bounds_write: assert property
    (@(posedge clk_i) disable iff (!rst_ni)
        (data_req_i && data_gnt_o && data_we_i |->
        (data_addr_i >= STDOUT_BASE && data_addr_i < STDOUT_BASE + STDOUT_LEN)
        || (data_addr_i >= DEBUG_BASE && data_addr_i < DEBUG_BASE + DEBUG_LEN)
        || (data_addr_i >= SRAM_BASE && data_addr_i < SRAM_BASE + SRAM_LEN)
        || (data_addr_i >= 0 && data_addr_i < SRAM_LEN)))
        else $error("out of bounds write to %08x with %08x",
                    data_addr_i, data_wdata_i);

   out_of_bounds_read: assert property
    (@(posedge clk_i) disable iff (!rst_ni)
        (select_rdata_q != UNMAP))
        else $error("out of bounds read");
`endif

    // make sure we select the proper read data
    always_comb begin: read_mux_sb_data_instr
        data_rdata_o  = '0;
        sb_rdata_o    = '0;
        instr_rdata_o = ram_instr_rdata;

        if(select_rdata_q == RAM) begin
            data_rdata_o = ram_data_rdata;
            sb_rdata_o   = ram_data_rdata;

        end else if (select_rdata_q == DEBUG) begin
            data_rdata_o  = dm_rdata;
            sb_rdata_o    = dm_rdata; //TODO: not possible
            instr_rdata_o = dm_rdata;

        end else if (select_rdata_q == ROM) begin
            // either we got into a loop for jtag booting or we jumpt to the l2
            // boot address (1c00_0080 === 0000_0080) to run a firmware directly
            if (JTAG_BOOT) begin
                data_rdata_o    = 32'b00000000000000000000000001101111; //while(true)
                sb_rdata_o      = 32'b00000000000000000000000001101111;
                instr_rdata_o   = 32'b00000000000000000000000001101111;
            end else begin
                data_rdata_o  = rom_rdata; //jal(5'b0, 21'h80); // jump to 0x0 + 0x80
                sb_rdata_o    = rom_rdata; //jal(5'b0, 21'h80);
                instr_rdata_o = rom_rdata; //jal(5'b0, 21'h80);
            end

        end else if (select_rdata_q == IDLE_READ) begin
        end
    end

    // print to stdout pseudo peripheral
    always_ff @(posedge clk_i, negedge rst_ni) begin: print_peripheral
        if(print_valid) begin
            if ($test$plusargs("verbose")) begin
                if (32 <= print_wdata && print_wdata < 128)
                    $display("OUT: '%c'", print_wdata[7:0]);
                else
                    $display("OUT: %3d", print_wdata);

            end else begin
                $write("%c", print_wdata[7:0]);
`ifndef VERILATOR
                $fflush();
`endif
            end
        end
    end

    assign irq_id_o = TIMER_IRQ_ID;
    assign irq_o = irq_q;

    // Control timer. We need one to have some kind of timeout for tests that
    // get stuck in some loop. The riscv-tests also mandate that. Enable timer
    // interrupt by writing 1 to timer_irq_mask_q. Write initial value to
    // timer_cnt_q which gets counted down each cycle. When it transitions from
    // 1 to 0, and interrupt request (irq_q) is made (masked by timer_irq_mask_q).
    always_ff @(posedge clk_i, negedge rst_ni) begin: tb_timer
        if(~rst_ni) begin
            timer_irq_mask_q <= '0;
            timer_cnt_q      <= '0;
            irq_q            <= '0;

        end else begin
            // set timer irq mask
            if(timer_reg_valid) begin
                timer_irq_mask_q <= timer_wdata;

            // write timer value
            end else if(timer_val_valid) begin
                timer_cnt_q <= timer_wdata;

            end else begin
                if(timer_cnt_q > 0)
                    timer_cnt_q <= timer_cnt_q - 1;

                if(timer_cnt_q == 1)
                    irq_q <= 1'b1 && timer_irq_mask_q[TIMER_IRQ_ID];

                if(irq_ack_i == 1'b1 && irq_id_i == TIMER_IRQ_ID)
                    irq_q <= '0;

            end
        end
    end

    // show writes if requested
    always_ff @(posedge clk_i, negedge rst_ni) begin: verbose_writes
        if ($test$plusargs("verbose") && data_req_i && data_we_i)
            $display("write addr=0x%08x: data=0x%08x",
                     data_addr_i, data_wdata_i);
    end

    // debug rom for booting directly to the firmware
    boot_rom boot_rom_i (
        .clk_i  ( clk_i     ),
        .req_i  ( rom_req   ),
        .addr_i ( rom_addr  ),
        .rdata_o( rom_rdata )
    );


    // instantiate the ram
    dp_ram #(
        .ADDR_WIDTH (RAM_ADDR_WIDTH),
        .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH)
    ) dp_ram_i (
        .clk_i     ( clk_i         ),

        .en_a_i    ( ram_instr_req                      ),
        .addr_a_i  ( ram_instr_addr[RAM_ADDR_WIDTH-1:0] ),
        .wdata_a_i ( '0                                 ),	// Not writing so ignored
        .rdata_a_o ( ram_instr_rdata                    ),
        .we_a_i    ( '0                                 ),
        .be_a_i    ( 4'b1111                            ),	// Always want 32-bits

        .en_b_i    ( ram_data_req    ),
        .addr_b_i  ( ram_data_addr   ),
        .wdata_b_i ( ram_data_wdata  ),
        .rdata_b_o ( ram_data_rdata  ),
        .we_b_i    ( ram_data_we     ),
        .be_b_i    ( ram_data_be     )
     );

    // do the handshacking stuff by assuming we always react in one cycle
    assign dm_req_o    = dm_req;
    assign dm_addr_o   = dm_addr;
    assign dm_we_o     = dm_we;
    assign dm_be_o     = dm_be;
    assign dm_wdata_o  = dm_wdata;
    assign dm_rdata    = dm_rdata_i;
    assign dm_rvalid   = dm_rvalid_i; // TODO: we dont' care about this
    assign dm_gnt      = dm_gnt_i; // TODO: we don't care about this


    // sb and core rvalid
    assign data_rvalid_o    = data_rvalid_q;
    assign sb_rvalid_o      = sb_rvalid_q;
    assign instr_rvalid_o   = instr_rvalid_q;


    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            select_rdata_q <= IDLE_READ;
            select_wdata_q <= IDLE_WRITE;

            data_rvalid_q  <= '0;
            sb_rvalid_q    <= '0;
            instr_rvalid_q <= '0;

        end else begin
            select_rdata_q <= select_rdata_d;
            select_wdata_q <= select_wdata_d;

            data_rvalid_q  <= data_rvalid_d;
            sb_rvalid_q    <= sb_rvalid_d;
            instr_rvalid_q <= instr_rvalid_d;

        end
    end

endmodule // ram
