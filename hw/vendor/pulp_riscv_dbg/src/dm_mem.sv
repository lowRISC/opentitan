/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_mem.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   11.7.2018
 *
 * Description: Memory module for execution-based debug clients
 *
 */

module dm_mem #(
    parameter int                 NrHarts          = -1,
    parameter int                 BusWidth         = -1,
    parameter logic [NrHarts-1:0] SelectableHarts  = -1
)(
    input  logic                             clk_i,       // Clock
    input  logic                             rst_ni,      // debug module reset

    output logic [NrHarts-1:0]               debug_req_o,
    input  logic [19:0]                      hartsel_i,
    // from Ctrl and Status register
    input  logic [NrHarts-1:0]               haltreq_i,
    input  logic [NrHarts-1:0]               resumereq_i,
    input  logic                             clear_resumeack_i,

    // state bits
    output logic [NrHarts-1:0]               halted_o,    // hart acknowledge halt
    output logic [NrHarts-1:0]               resuming_o,  // hart is resuming

    input  logic [dm::ProgBufSize-1:0][31:0] progbuf_i,    // program buffer to expose

    input  logic [dm::DataCount-1:0][31:0]   data_i,       // data in
    output logic [dm::DataCount-1:0][31:0]   data_o,       // data out
    output logic                             data_valid_o, // data out is valid
    // abstract command interface
    input  logic                             cmd_valid_i,
    input  dm::command_t                     cmd_i,
    output logic                             cmderror_valid_o,
    output dm::cmderr_e                      cmderror_o,
    output logic                             cmdbusy_o,
    // data interface

    // SRAM interface
    input  logic                             req_i,
    input  logic                             we_i,
    input  logic [BusWidth-1:0]              addr_i,
    input  logic [BusWidth-1:0]              wdata_i,
    input  logic [BusWidth/8-1:0]            be_i,
    output logic [BusWidth-1:0]              rdata_o
);

    localparam int HartSelLen = (NrHarts == 1) ? 1 : $clog2(NrHarts);
    localparam int MaxAar = (BusWidth == 64) ? 4 : 3;
    localparam DbgAddressBits = 12;
    localparam logic [DbgAddressBits-1:0] DataBase = (dm::DataAddr);
    localparam logic [DbgAddressBits-1:0] DataEnd = (dm::DataAddr + 4*dm::DataCount);
    localparam logic [DbgAddressBits-1:0] ProgBufBase = (dm::DataAddr - 4*dm::ProgBufSize);
    localparam logic [DbgAddressBits-1:0] ProgBufEnd = (dm::DataAddr - 1);
    localparam logic [DbgAddressBits-1:0] AbstractCmdBase = (ProgBufBase - 4*10);
    localparam logic [DbgAddressBits-1:0] AbstractCmdEnd = (ProgBufBase - 1);
    localparam logic [DbgAddressBits-1:0] WhereTo   = 'h300;
    localparam logic [DbgAddressBits-1:0] FlagsBase = 'h400;
    localparam logic [DbgAddressBits-1:0] FlagsEnd  = 'h7FF;


    localparam logic [DbgAddressBits-1:0] Halted    = 'h100;
    localparam logic [DbgAddressBits-1:0] Going     = 'h104;
    localparam logic [DbgAddressBits-1:0] Resuming  = 'h108;
    localparam logic [DbgAddressBits-1:0] Exception = 'h10C;

    logic [dm::ProgBufSize/2-1:0][63:0]   progbuf;
    logic [4:0][63:0]   abstract_cmd;
    logic [NrHarts-1:0] halted_d, halted_q;
    logic [NrHarts-1:0] resuming_d, resuming_q;
    logic               resume, go, going;
    logic [NrHarts-1:0] halted;

    logic [HartSelLen-1:0] hart_sel;
    logic exception;
    logic unsupported_command;

    logic [63:0] rom_rdata;
    logic [63:0] rdata_d, rdata_q;
    logic        word_enable32_q;

    // distinguish whether we need to forward data from the ROM or the FSM
    // latch the address for this
    logic fwd_rom_d, fwd_rom_q;
    dm::ac_ar_cmd_t ac_ar;

    // Abstract Command Access Register
    assign ac_ar       = dm::ac_ar_cmd_t'(cmd_i.control);
    assign hart_sel    = wdata_i[HartSelLen-1:0];
    assign debug_req_o = haltreq_i;
    assign halted_o    = halted_q;
    assign resuming_o  = resuming_q;

    // reshape progbuf
    assign progbuf = progbuf_i;

    typedef enum logic [1:0] { Idle, Go, Resume, CmdExecuting } state_e;
    state_e state_d, state_q;

    // hart ctrl queue
    always_comb begin
        cmderror_valid_o = 1'b0;
        cmderror_o       = dm::CmdErrNone;
        state_d          = state_q;
        go               = 1'b0;
        resume           = 1'b0;
        cmdbusy_o        = 1'b1;

        case (state_q)
            Idle: begin
                cmdbusy_o = 1'b0;
                if (cmd_valid_i && halted_q[hartsel_i]) begin
                    // give the go signal
                    state_d = Go;
                end else if (cmd_valid_i) begin
                    // hart must be halted for all requests
                    cmderror_valid_o = 1'b1;
                    cmderror_o = dm::CmdErrorHaltResume;
                end
                // CSRs want to resume, the request is ignored when the hart is
                // requested to halt or it didn't clear the resuming_q bit before
                if (resumereq_i[hartsel_i] && !resuming_q[hartsel_i] &&
                     !haltreq_i[hartsel_i] &&    halted_q[hartsel_i]) begin
                    state_d = Resume;
                end
            end

            Go: begin
                // we are already busy here since we scheduled the execution of a program
                cmdbusy_o = 1'b1;
                go        = 1'b1;
                // the thread is now executing the command, track its state
                if (going)
                    state_d = CmdExecuting;
            end

            Resume: begin
                cmdbusy_o = 1'b1;
                resume = 1'b1;
                if (resuming_o[hartsel_i])
                    state_d = Idle;
            end

            CmdExecuting: begin
                cmdbusy_o = 1'b1;
                go        = 1'b0;
                // wait until the hart has halted again
                if (halted[hartsel_i]) begin
                    state_d = Idle;
                end
            end
        endcase

        // only signal once that cmd is unsupported so that we can clear cmderr
        // in subsequent writes to abstractcs
        if (unsupported_command && cmd_valid_i) begin
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrNotSupported;
        end

        if (exception) begin
            cmderror_valid_o = 1'b1;
            cmderror_o = dm::CmdErrorException;
        end

    end

    // read/write logic
    always_comb begin
        automatic logic [63:0] data_bits;

        halted_d     = halted_q;
        resuming_d   = resuming_q;
        rdata_o      = (BusWidth == 64) ?
                          (fwd_rom_q ? rom_rdata : rdata_q) :
                          (word_enable32_q ?
                              (fwd_rom_q ? rom_rdata[63:32] : rdata_q[63:32]) :
                              (fwd_rom_q ? rom_rdata[31: 0] : rdata_q[31: 0]));
        rdata_d      = rdata_q;
        // convert the data in bits representation
        data_bits    = data_i;
        // write data in csr register
        data_valid_o = 1'b0;
        exception    = 1'b0;
        halted       = '0;
        going        = 1'b0;
        // The resume ack signal is lowered when the resume request is deasserted
        if (clear_resumeack_i) begin
            resuming_d[hartsel_i] = 1'b0;
        end
        // we've got a new request
        if (req_i) begin
            // this is a write
            if (we_i) begin
                unique case (addr_i[DbgAddressBits-1:0]) inside
                    Halted: begin
                        halted[hart_sel] = 1'b1;
                        halted_d[hart_sel] = 1'b1;
                    end
                    Going: begin
                        going = 1'b1;
                    end
                    Resuming: begin
                        // clear the halted flag as the hart resumed execution
                        halted_d[hart_sel] = 1'b0;
                        // set the resuming flag which needs to be cleared by the debugger
                        resuming_d[hart_sel] = 1'b1;
                    end
                    // an exception occurred during execution
                    Exception: exception = 1'b1;
                    // core can write data registers
                    [(dm::DataAddr):DataEnd]: begin
                        data_valid_o = 1'b1;
                        for (int i = 0; i < $bits(be_i); i++) begin
                            if (be_i[i]) begin
                                data_bits[i*8+:8] = wdata_i[i*8+:8];
                            end
                        end
                    end
                    default ;
                endcase

            // this is a read
            end else begin
                unique case (addr_i[DbgAddressBits-1:0]) inside
                    // variable ROM content
                    WhereTo: begin
                        // variable jump to abstract cmd, program_buffer or resume
                        if (resumereq_i[hart_sel]) begin
                            rdata_d = {32'b0, dm::jal('0, dm::ResumeAddress[11:0]-WhereTo)};
                        end

                        // there is a command active so jump there
                        if (cmdbusy_o) begin
                            // transfer not set is shortcut to the program buffer if postexec is set
                            // keep this statement narrow to not catch invalid commands
                            if (cmd_i.cmdtype == dm::AccessRegister &&
                                !ac_ar.transfer && ac_ar.postexec) begin
                                rdata_d = {32'b0, dm::jal('0, ProgBufBase-WhereTo)};
                            // this is a legit abstract cmd -> execute it
                            end else begin
                                rdata_d = {32'b0, dm::jal('0, AbstractCmdBase-WhereTo)};
                            end
                        end
                    end

                    [DataBase:DataEnd]: begin
                        rdata_d = {
                                  data_i[(addr_i[DbgAddressBits-1:3] - DataBase[DbgAddressBits-1:3] + 1)],
                                  data_i[(addr_i[DbgAddressBits-1:3] - DataBase[DbgAddressBits-1:3])]
                                  };
                    end

                    [ProgBufBase:ProgBufEnd]: begin
                        rdata_d = progbuf[(addr_i[DbgAddressBits-1:3] -
                                      ProgBufBase[DbgAddressBits-1:3])];
                    end

                    // two slots for abstract command
                    [AbstractCmdBase:AbstractCmdEnd]: begin
                        // return the correct address index
                        rdata_d = abstract_cmd[(addr_i[DbgAddressBits-1:3] -
                                       AbstractCmdBase[DbgAddressBits-1:3])];
                    end
                    // harts are polling for flags here
                    [FlagsBase:FlagsEnd]: begin
                        automatic logic [7:0][7:0] rdata;
                        rdata = '0;
                        // release the corresponding hart
                        if (({addr_i[DbgAddressBits-1:3], 3'b0} - FlagsBase[DbgAddressBits-1:0]) ==
                          {hartsel_i[DbgAddressBits-1:3], 3'b0}) begin
                            rdata[hartsel_i[2:0]] = {6'b0, resume, go};
                        end
                        rdata_d = rdata;
                    end
                    default: ;
                endcase
            end
        end

        data_o = data_bits;
    end

    always_comb begin : abstract_cmd_rom
        // this abstract command is currently unsupported
        unsupported_command = 1'b0;
        // default memory
        // if ac_ar.transfer is not set then we can take a shortcut to the program buffer
        abstract_cmd[0][31:0]  = dm::illegal();
        // load debug module base address into a0, this is shared among all commands
        abstract_cmd[0][63:32] = dm::auipc(5'd10, '0);
        abstract_cmd[1][31:0]  = dm::srli(5'd10, 5'd10, 6'd12); // clr lowest 12b -> DM base offset
        abstract_cmd[1][63:32] = dm::slli(5'd10, 5'd10, 6'd12);
        abstract_cmd[2][31:0]  = dm::nop();
        abstract_cmd[2][63:32] = dm::nop();
        abstract_cmd[3][31:0]  = dm::nop();
        abstract_cmd[3][63:32] = dm::nop();
        abstract_cmd[4][31:0]  = dm::csrr(dm::CSR_DSCRATCH1, 5'd10);
        abstract_cmd[4][63:32] = dm::ebreak();

        // this depends on the command being executed
        unique case (cmd_i.cmdtype)
            // --------------------
            // Access Register
            // --------------------
            dm::AccessRegister: begin
                if (ac_ar.aarsize < MaxAar && ac_ar.transfer && ac_ar.write) begin
                    // store a0 in dscratch1
                    abstract_cmd[0][31:0] = dm::csrw(dm::CSR_DSCRATCH1, 5'd10);
                    // this range is reserved
                    if (ac_ar.regno[15:14] != '0) begin
                        abstract_cmd[0][31:0] = dm::ebreak(); // we leave asap
                        unsupported_command = 1'b1;
                    // A0 access needs to be handled separately, as we use A0 to load
                    // the DM address offset need to access DSCRATCH1 in this case
                    end else if (ac_ar.regno[12] && (!ac_ar.regno[5]) &&
                                (ac_ar.regno[4:0] == 5'd10)) begin
                        // store s0 in dscratch
                        abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
                        // load from data register
                        abstract_cmd[2][63:32] = dm::load(ac_ar.aarsize, 5'd8, 5'd10, dm::DataAddr);
                        // and store it in the corresponding CSR
                        abstract_cmd[3][31:0]  = dm::csrw(dm::CSR_DSCRATCH1, 5'd8);
                        // restore s0 again from dscratch
                        abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
                    // GPR/FPR access
                    end else if (ac_ar.regno[12]) begin
                        // determine whether we want to access the floating point register or not
                        if (ac_ar.regno[5]) begin
                            abstract_cmd[2][31:0] =
                                dm::float_load(ac_ar.aarsize, ac_ar.regno[4:0], 5'd10, dm::DataAddr);
                        end else begin
                            abstract_cmd[2][31:0] =
                                dm::load(ac_ar.aarsize, ac_ar.regno[4:0], 5'd10, dm::DataAddr);
                        end
                    // CSR access
                    end else begin
                        // data register to CSR
                        // store s0 in dscratch
                        abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
                        // load from data register
                        abstract_cmd[2][63:32] = dm::load(ac_ar.aarsize, 5'd8, 5'd10, dm::DataAddr);
                        // and store it in the corresponding CSR
                        abstract_cmd[3][31:0]  = dm::csrw(dm::csr_reg_t'(ac_ar.regno[11:0]), 5'd8);
                        // restore s0 again from dscratch
                        abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
                    end
                end else if (ac_ar.aarsize < MaxAar && ac_ar.transfer && !ac_ar.write) begin
                    // store a0 in dscratch1
                    abstract_cmd[0][31:0]  = dm::csrw(dm::CSR_DSCRATCH1, 5'd10);
                    // this range is reserved
                    if (ac_ar.regno[15:14] != '0) begin
                        abstract_cmd[0][31:0] = dm::ebreak(); // we leave asap
                        unsupported_command = 1'b1;
                    // A0 access needs to be handled separately, as we use A0 to load
                    // the DM address offset need to access DSCRATCH1 in this case
                    end else if (ac_ar.regno[12] && (!ac_ar.regno[5]) &&
                                (ac_ar.regno[4:0] == 5'd10)) begin
                        // store s0 in dscratch
                        abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
                        // read value from CSR into s0
                        abstract_cmd[2][63:32] = dm::csrr(dm::CSR_DSCRATCH1, 5'd8);
                        // and store s0 into data section
                        abstract_cmd[3][31:0]  = dm::store(ac_ar.aarsize, 5'd8, 5'd10, dm::DataAddr);
                        // restore s0 again from dscratch
                        abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
                    // GPR/FPR access
                    end else if (ac_ar.regno[12]) begin
                        // determine whether we want to access the floating point register or not
                        if (ac_ar.regno[5]) begin
                            abstract_cmd[2][31:0] =
                                dm::float_store(ac_ar.aarsize, ac_ar.regno[4:0], 5'd10, dm::DataAddr);
                        end else begin
                            abstract_cmd[2][31:0] =
                                dm::store(ac_ar.aarsize, ac_ar.regno[4:0], 5'd10, dm::DataAddr);
                        end
                    // CSR access
                    end else begin
                        // CSR register to data
                        // store s0 in dscratch
                        abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
                        // read value from CSR into s0
                        abstract_cmd[2][63:32] = dm::csrr(dm::csr_reg_t'(ac_ar.regno[11:0]), 5'd8);
                        // and store s0 into data section
                        abstract_cmd[3][31:0]  = dm::store(ac_ar.aarsize, 5'd8, 5'd10, dm::DataAddr);
                        // restore s0 again from dscratch
                        abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
                    end
                end else if (ac_ar.aarsize >= MaxAar || ac_ar.aarpostincrement == 1'b1) begin
                    // this should happend when e.g. ac_ar.aarsize >= MaxAar
                    // Openocd will try to do an access with aarsize=64 bits
                    // first before falling back to 32 bits.
                    abstract_cmd[0][31:0] = dm::ebreak(); // we leave asap
                    unsupported_command = 1'b1;

                end

                // Check whether we need to execute the program buffer. When we
                // get an unsupported command we really should abort instead of
                // still trying to execute the program buffer, makes it easier
                // for the debugger to recover
                if (ac_ar.postexec && !unsupported_command) begin
                    // issue a nop, we will automatically run into the program buffer
                    abstract_cmd[4][63:32] = dm::nop();
                end

            end
            // not supported at the moment
            // dm::QuickAccess:;
            // dm::AccessMemory:;
            default: begin
                abstract_cmd[0][31:0] = dm::ebreak();
                unsupported_command = 1'b1;
            end
        endcase
    end

    logic [63:0] rom_addr;
    assign rom_addr = 64'(addr_i);
    debug_rom i_debug_rom (
        .clk_i,
        .req_i,
        .addr_i  ( rom_addr  ),
        .rdata_o ( rom_rdata )
    );

    // ROM starts at the HaltAddress of the core e.g.: it immediately jumps to
    // the ROM base address
    assign fwd_rom_d = (addr_i[DbgAddressBits-1:0] >= dm::HaltAddress[DbgAddressBits-1:0]) ?
                           1'b1 : 1'b0;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            fwd_rom_q       <= 1'b0;
            rdata_q         <= '0;
            state_q         <= Idle;
            word_enable32_q <= 1'b0;
        end else begin
            fwd_rom_q       <= fwd_rom_d;
            rdata_q         <= rdata_d;
            state_q         <= state_d;
            word_enable32_q <= addr_i[2];
        end
    end

    for (genvar k = 0; k < NrHarts; k++) begin : gen_halted
        always_ff @(posedge clk_i or negedge rst_ni) begin
            if (!rst_ni) begin
                halted_q[k]   <= 1'b0;
                resuming_q[k] <= 1'b0;
            end else begin
                halted_q[k]   <= SelectableHarts[k] ? halted_d[k]   : 1'b0;
                resuming_q[k] <= SelectableHarts[k] ? resuming_d[k] : 1'b0;
            end
        end
    end

endmodule
