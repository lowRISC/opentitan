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
  parameter int unsigned        NrHarts          =  1,
  parameter int unsigned        BusWidth         = 32,
  parameter logic [NrHarts-1:0] SelectableHarts  = {NrHarts{1'b1}},
  parameter int unsigned        DmBaseAddress    = '0,
  localparam int unsigned       BeWidth          = BusWidth/8
) (
  input  logic                             clk_i,       // Clock
  input  logic                             rst_ni,      // debug module reset

  output logic [NrHarts-1:0]               debug_req_o,
  input  logic                             ndmreset_i,
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
  input  logic [BeWidth-1:0]               be_i,
  output logic [BusWidth-1:0]              rdata_o,
  output logic                             err_o
);
  localparam int unsigned DbgAddressBits = 12;
  localparam int unsigned HartSelLen     = (NrHarts == 1) ? 1 : $clog2(NrHarts);
  localparam int unsigned NrHartsAligned = 2**HartSelLen;
  localparam int unsigned MaxAar         = (BusWidth == 64) ? 4 : 3;
  localparam bit          HasSndScratch  = (DmBaseAddress != 0);
  // Depending on whether we are at the zero page or not we either use `x0` or `x10/a0`
  localparam logic [4:0]  LoadBaseAddr   = (DmBaseAddress == 0) ? 5'd0 : 5'd10;

  localparam logic [DbgAddressBits-1:0] DataBaseAddr        = (dm::DataAddr);
  localparam logic [DbgAddressBits-1:0] DataEndAddr         = (dm::DataAddr + 4*dm::DataCount - 1);
  localparam logic [DbgAddressBits-1:0] ProgBufBaseAddr     = (dm::DataAddr - 4*dm::ProgBufSize);
  localparam logic [DbgAddressBits-1:0] ProgBufEndAddr      = (dm::DataAddr - 1);
  localparam logic [DbgAddressBits-1:0] AbstractCmdBaseAddr = (ProgBufBaseAddr - 4*10);
  localparam logic [DbgAddressBits-1:0] AbstractCmdEndAddr  = (ProgBufBaseAddr - 1);

  localparam logic [DbgAddressBits-1:0] WhereToAddr   = 'h300;
  localparam logic [DbgAddressBits-1:0] FlagsBaseAddr = 'h400;
  localparam logic [DbgAddressBits-1:0] FlagsEndAddr  = 'h7FF;

  localparam logic [DbgAddressBits-1:0] HaltedAddr    = 'h100;
  localparam logic [DbgAddressBits-1:0] GoingAddr     = 'h108;
  localparam logic [DbgAddressBits-1:0] ResumingAddr  = 'h110;
  localparam logic [DbgAddressBits-1:0] ExceptionAddr = 'h118;

  localparam logic [DbgAddressBits-1:0] RomBaseAddr   = dm::HaltAddress;
  // The size is arbitrarily set to 0x800, so as to make the dm_space exactly 0x900 long. This is
  // more than eough to cover the 19 x 64bit = 0x98 bytes currenty allocated in the debug ROM.
  localparam logic [DbgAddressBits-1:0] RomEndAddr    = dm::HaltAddress + 'h7FF;

  logic [dm::ProgBufSize/2-1:0][63:0]   progbuf;
  logic [7:0][63:0]   abstract_cmd;
  logic [NrHarts-1:0] halted_d, halted_q;
  logic [NrHarts-1:0] resuming_d, resuming_q;
  logic               resume, go, going;

  logic exception;
  logic unsupported_command;

  logic [63:0] rom_rdata;
  logic [63:0] rdata_d, rdata_q;
  logic        word_enable32_q;

  // this is needed to avoid lint warnings related to array indexing
  // resize hartsel to valid range
  logic [HartSelLen-1:0] hartsel, wdata_hartsel;

  assign hartsel       = hartsel_i[HartSelLen-1:0];
  assign wdata_hartsel = wdata_i[HartSelLen-1:0];

  logic [NrHartsAligned-1:0] resumereq_aligned, haltreq_aligned,
                             halted_d_aligned, halted_q_aligned,
                             halted_aligned, resumereq_wdata_aligned,
                             resuming_d_aligned, resuming_q_aligned;

  assign resumereq_aligned       = NrHartsAligned'(resumereq_i);
  assign haltreq_aligned         = NrHartsAligned'(haltreq_i);
  assign resumereq_wdata_aligned = NrHartsAligned'(resumereq_i);

  assign halted_q_aligned        = NrHartsAligned'(halted_q);
  assign halted_d                = NrHarts'(halted_d_aligned);
  assign resuming_q_aligned      = NrHartsAligned'(resuming_q);
  assign resuming_d              = NrHarts'(resuming_d_aligned);

  // distinguish whether we need to forward data from the ROM or the FSM
  // latch the address for this
  logic fwd_rom_d, fwd_rom_q;
  dm::ac_ar_cmd_t ac_ar;

  // Abstract Command Access Register
  assign ac_ar       = dm::ac_ar_cmd_t'(cmd_i.control);
  assign debug_req_o = haltreq_i;
  assign halted_o    = halted_q;
  assign resuming_o  = resuming_q;

  // reshape progbuf
  assign progbuf = progbuf_i;

  typedef enum logic [1:0] { Idle, Go, Resume, CmdExecuting } state_e;
  state_e state_d, state_q;

  // hart ctrl queue
  always_comb begin : p_hart_ctrl_queue
    cmderror_valid_o = 1'b0;
    cmderror_o       = dm::CmdErrNone;
    state_d          = state_q;
    go               = 1'b0;
    resume           = 1'b0;
    cmdbusy_o        = 1'b1;

    unique case (state_q)
      Idle: begin
        cmdbusy_o = 1'b0;
        if (cmd_valid_i && halted_q_aligned[hartsel] && !unsupported_command) begin
          // give the go signal
          state_d = Go;
        end else if (cmd_valid_i) begin
          // hart must be halted for all requests
          cmderror_valid_o = 1'b1;
          cmderror_o = dm::CmdErrorHaltResume;
        end
        // CSRs want to resume, the request is ignored when the hart is
        // requested to halt or it didn't clear the resuming_q bit before
        if (resumereq_aligned[hartsel] && !resuming_q_aligned[hartsel] &&
            !haltreq_aligned[hartsel] && halted_q_aligned[hartsel]) begin
          state_d = Resume;
        end
      end

      Go: begin
        // we are already busy here since we scheduled the execution of a program
        cmdbusy_o = 1'b1;
        go        = 1'b1;
        // the thread is now executing the command, track its state
        if (going) begin
            state_d = CmdExecuting;
        end
      end

      Resume: begin
        cmdbusy_o = 1'b1;
        resume = 1'b1;
        if (resuming_q_aligned[hartsel]) begin
          state_d = Idle;
        end
      end

      CmdExecuting: begin
        cmdbusy_o = 1'b1;
        go        = 1'b0;
        // wait until the hart has halted again
        if (halted_aligned[hartsel]) begin
          state_d = Idle;
        end
      end

      default: ;
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

    if (ndmreset_i) begin
      // Clear state of hart and its control signals when it is being reset.
      state_d = Idle;
      go      = 1'b0;
      resume  = 1'b0;
    end
  end

  // word mux for 32bit and 64bit buses
  logic [63:0] word_mux;
  assign word_mux = (fwd_rom_q) ? rom_rdata : rdata_q;

  if (BusWidth == 64) begin : gen_word_mux64
    assign rdata_o = word_mux;
  end else begin : gen_word_mux32
    assign rdata_o = (word_enable32_q) ? word_mux[32 +: 32] : word_mux[0 +: 32];
  end

  // read/write logic
  logic [dm::DataCount-1:0][31:0] data_bits;
  logic [7:0][7:0] rdata;
  always_comb begin : p_rw_logic

    halted_d_aligned   = NrHartsAligned'(halted_q);
    resuming_d_aligned = NrHartsAligned'(resuming_q);
    rdata_d        = rdata_q;
    data_bits      = data_i;
    rdata          = '0;
    fwd_rom_d      = 1'b0;

    // write data in csr register
    data_valid_o   = 1'b0;
    exception      = 1'b0;
    halted_aligned     = '0;
    going          = 1'b0;

    // The resume ack signal is lowered when the resume request is deasserted
    if (clear_resumeack_i) begin
      resuming_d_aligned[hartsel] = 1'b0;
    end
    // we've got a new request
    if (req_i) begin
      // this is a write
      if (we_i) begin
        unique case (addr_i[DbgAddressBits-1:0]) inside
          HaltedAddr: begin
            halted_aligned[wdata_hartsel] = 1'b1;
            halted_d_aligned[wdata_hartsel] = 1'b1;
          end
          GoingAddr: begin
            going = 1'b1;
          end
          ResumingAddr: begin
            // clear the halted flag as the hart resumed execution
            halted_d_aligned[wdata_hartsel] = 1'b0;
            // set the resuming flag which needs to be cleared by the debugger
            resuming_d_aligned[wdata_hartsel] = 1'b1;
          end
          // an exception occurred during execution
          ExceptionAddr: exception = 1'b1;
          // core can write data registers
          [DataBaseAddr:DataEndAddr]: begin
            data_valid_o = 1'b1;
            for (int unsigned dc = 0; dc < dm::DataCount; dc++) begin
              if ((addr_i[DbgAddressBits-1:2] - DataBaseAddr[DbgAddressBits-1:2]) == dc) begin
                for (int unsigned i = 0; i < $bits(be_i); i++) begin
                  if (be_i[i]) begin
                    if (i>3) begin // for upper 32bit data write (only used for BusWidth ==  64)
                      // ensure we write to an implemented data register
                      if (dc < (dm::DataCount - 1)) begin
                        data_bits[dc+1][(i-4)*8+:8] = wdata_i[i*8+:8];
                      end
                    end else begin // for lower 32bit data write
                      data_bits[dc][i*8+:8] = wdata_i[i*8+:8];
                    end
                  end
                end
              end
            end
          end
          default: ;
        endcase

      // this is a read
      end else begin
        unique case (addr_i[DbgAddressBits-1:0]) inside
          // variable ROM content
          WhereToAddr: begin
            // variable jump to abstract cmd, program_buffer or resume
            if (resumereq_wdata_aligned[wdata_hartsel]) begin
              rdata_d = {32'b0, dm::jal('0, 21'(dm::ResumeAddress[11:0])-21'(WhereToAddr))};
            end

            // there is a command active so jump there
            if (cmdbusy_o) begin
              // transfer not set is shortcut to the program buffer if postexec is set
              // keep this statement narrow to not catch invalid commands
              if (cmd_i.cmdtype == dm::AccessRegister &&
                  !ac_ar.transfer && ac_ar.postexec) begin
                rdata_d = {32'b0, dm::jal('0, 21'(ProgBufBaseAddr)-21'(WhereToAddr))};
              // this is a legit abstract cmd -> execute it
              end else begin
                rdata_d = {32'b0, dm::jal('0, 21'(AbstractCmdBaseAddr)-21'(WhereToAddr))};
              end
            end
          end

          [DataBaseAddr:DataEndAddr]: begin
            rdata_d = {
                      data_i[$clog2(dm::DataCount)'(((addr_i[DbgAddressBits-1:3]
                                                      - DataBaseAddr[DbgAddressBits-1:3]) << 1)
                                                    + 1'b1)],
                      data_i[$clog2(dm::DataCount)'(((addr_i[DbgAddressBits-1:3]
                                                      - DataBaseAddr[DbgAddressBits-1:3]) << 1))]
                      };
          end

          [ProgBufBaseAddr:ProgBufEndAddr]: begin
            rdata_d = progbuf[$clog2(dm::ProgBufSize)'(addr_i[DbgAddressBits-1:3] -
                          ProgBufBaseAddr[DbgAddressBits-1:3])];
          end

          // two slots for abstract command
          [AbstractCmdBaseAddr:AbstractCmdEndAddr]: begin
            // return the correct address index
            rdata_d = abstract_cmd[3'(addr_i[DbgAddressBits-1:3] -
                           AbstractCmdBaseAddr[DbgAddressBits-1:3])];
          end
          // harts are polling for flags here
          [FlagsBaseAddr:FlagsEndAddr]: begin
            // release the corresponding hart
            if (({addr_i[DbgAddressBits-1:3], 3'b0} - FlagsBaseAddr[DbgAddressBits-1:0]) ==
              (DbgAddressBits'(hartsel) & {{(DbgAddressBits-3){1'b1}}, 3'b0})) begin
              rdata[DbgAddressBits'(hartsel) & DbgAddressBits'(3'b111)] = {6'b0, resume, go};
            end
            rdata_d = rdata;
          end
          // Access has to be forwarded to the ROM. The ROM starts at the HaltAddress of the core
          // e.g.: it immediately jumps to the ROM base address.
          [RomBaseAddr:RomEndAddr]: begin
            fwd_rom_d = 1'b1;
          end
          default: ;
        endcase
      end
    end

    if (ndmreset_i) begin
      // When harts are reset, they are neither halted nor resuming.
      halted_d_aligned   = '0;
      resuming_d_aligned = '0;
    end

    data_o = data_bits;
  end

  // This flags subword writes that are shorter than the defined width of the register.
  // Other writes are ignored.
  function automatic logic gen_wr_err(logic we, logic [BeWidth-1:0] be, logic [BeWidth-1:0] mask);
    return we && (|(~be & mask));
  endfunction

  // Relevant bus error cases
  // - access unmapped address
  // - write a CSR with unaligned address, e.g. `a_address[1:0] != 0`
  // - write a CSR less than its width, e.g. when CSR is 2 bytes wide, only write 1 byte
  // - write a RO (read-only) memory
  localparam logic[BeWidth-1:0] FullRegMask = {BeWidth{1'b1}};
  localparam logic[BeWidth-1:0] OneBitMask  = BeWidth'(1'b1);
  localparam logic[BeWidth-1:0] HartSelMask = BeWidth'(2**HartSelLen-1);
  logic err_d, err_q;
  always_comb begin
    err_d = 1'b0;
    if (req_i) begin
      unique case (addr_i[DbgAddressBits-1:0]) inside
        WhereToAddr:                              err_d = gen_wr_err(we_i, be_i, FullRegMask);
        HaltedAddr:                               err_d = gen_wr_err(we_i, be_i, HartSelMask);
        GoingAddr:                                err_d = gen_wr_err(we_i, be_i, OneBitMask);
        ResumingAddr:                             err_d = gen_wr_err(we_i, be_i, HartSelMask);
        ExceptionAddr:                            err_d = gen_wr_err(we_i, be_i, OneBitMask);
        [DataBaseAddr:DataEndAddr]:               err_d = gen_wr_err(we_i, be_i, FullRegMask);
        [ProgBufBaseAddr:ProgBufEndAddr]:         err_d = gen_wr_err(we_i, be_i, FullRegMask);
        [AbstractCmdBaseAddr:AbstractCmdEndAddr]: err_d = gen_wr_err(we_i, be_i, FullRegMask);
        [FlagsBaseAddr:FlagsEndAddr]:             err_d = gen_wr_err(we_i, be_i, FullRegMask);
        [RomBaseAddr:RomEndAddr]:                 err_d = we_i; // Writing ROM area always errors.
        default: err_d = 1'b1;
      endcase
      // Unaligned accesses
      if (addr_i[$clog2(BeWidth)-1:0] != '0) begin
        err_d = 1'b1;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_err_reg
    if (!rst_ni) begin
      err_q <= 1'b0;
    end else begin
      err_q <= err_d;
    end
  end

  assign err_o = err_q;

  always_comb begin : p_abstract_cmd_rom
    // this abstract command is currently unsupported
    unsupported_command = 1'b0;
    // default memory
    // if ac_ar.transfer is not set then we can take a shortcut to the program buffer
    abstract_cmd[0][31:0]  = dm::illegal();
    // load debug module base address into a0, this is shared among all commands
    abstract_cmd[0][63:32] = HasSndScratch ? dm::auipc(5'd10, '0) : dm::nop();
    // clr lowest 12b -> DM base offset
    abstract_cmd[1][31:0]  = HasSndScratch ? dm::srli(5'd10, 5'd10, 6'd12) : dm::nop();
    abstract_cmd[1][63:32] = HasSndScratch ? dm::slli(5'd10, 5'd10, 6'd12) : dm::nop();
    abstract_cmd[2][31:0]  = dm::nop();
    abstract_cmd[2][63:32] = dm::nop();
    abstract_cmd[3][31:0]  = dm::nop();
    abstract_cmd[3][63:32] = dm::nop();
    abstract_cmd[4][31:0]  = HasSndScratch ? dm::csrr(dm::CSR_DSCRATCH1, 5'd10) : dm::nop();
    abstract_cmd[4][63:32] = dm::ebreak();
    abstract_cmd[7:5]      = '0;

    // this depends on the command being executed
    unique case (cmd_i.cmdtype)
      // --------------------
      // Access Register
      // --------------------
      dm::AccessRegister: begin
        if (32'(ac_ar.aarsize) < MaxAar && ac_ar.transfer && ac_ar.write) begin
          // store a0 in dscratch1
          abstract_cmd[0][31:0] = HasSndScratch ? dm::csrw(dm::CSR_DSCRATCH1, 5'd10) : dm::nop();
          // this range is reserved
          if (ac_ar.regno[15:14] != '0) begin
            abstract_cmd[0][31:0] = dm::ebreak(); // we leave asap
            unsupported_command = 1'b1;
          // A0 access needs to be handled separately, as we use A0 to load
          // the DM address offset need to access DSCRATCH1 in this case
          end else if (HasSndScratch && ac_ar.regno[12] && (!ac_ar.regno[5]) &&
                      (ac_ar.regno[4:0] == 5'd10)) begin
            // store s0 in dscratch
            abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
            // load from data register
            abstract_cmd[2][63:32] = dm::load(ac_ar.aarsize, 5'd8, LoadBaseAddr, dm::DataAddr);
            // and store it in the corresponding CSR
            abstract_cmd[3][31:0]  = dm::csrw(dm::CSR_DSCRATCH1, 5'd8);
            // restore s0 again from dscratch
            abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
          // GPR/FPR access
          end else if (ac_ar.regno[12]) begin
            // determine whether we want to access the floating point register or not
            if (ac_ar.regno[5]) begin
              abstract_cmd[2][31:0] =
                  dm::float_load(ac_ar.aarsize, ac_ar.regno[4:0], LoadBaseAddr, dm::DataAddr);
            end else begin
              abstract_cmd[2][31:0] =
                  dm::load(ac_ar.aarsize, ac_ar.regno[4:0], LoadBaseAddr, dm::DataAddr);
            end
          // CSR access
          end else begin
            // data register to CSR
            // store s0 in dscratch
            abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
            // load from data register
            abstract_cmd[2][63:32] = dm::load(ac_ar.aarsize, 5'd8, LoadBaseAddr, dm::DataAddr);
            // and store it in the corresponding CSR
            abstract_cmd[3][31:0]  = dm::csrw(dm::csr_reg_t'(ac_ar.regno[11:0]), 5'd8);
            // restore s0 again from dscratch
            abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
          end
        end else if (32'(ac_ar.aarsize) < MaxAar && ac_ar.transfer && !ac_ar.write) begin
          // store a0 in dscratch1
          abstract_cmd[0][31:0]  = HasSndScratch ?
                                   dm::csrw(dm::CSR_DSCRATCH1, LoadBaseAddr) :
                                   dm::nop();
          // this range is reserved
          if (ac_ar.regno[15:14] != '0) begin
              abstract_cmd[0][31:0] = dm::ebreak(); // we leave asap
              unsupported_command = 1'b1;
          // A0 access needs to be handled separately, as we use A0 to load
          // the DM address offset need to access DSCRATCH1 in this case
          end else if (HasSndScratch && ac_ar.regno[12] && (!ac_ar.regno[5]) &&
                      (ac_ar.regno[4:0] == 5'd10)) begin
            // store s0 in dscratch
            abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
            // read value from CSR into s0
            abstract_cmd[2][63:32] = dm::csrr(dm::CSR_DSCRATCH1, 5'd8);
            // and store s0 into data section
            abstract_cmd[3][31:0]  = dm::store(ac_ar.aarsize, 5'd8, LoadBaseAddr, dm::DataAddr);
            // restore s0 again from dscratch
            abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
          // GPR/FPR access
          end else if (ac_ar.regno[12]) begin
            // determine whether we want to access the floating point register or not
            if (ac_ar.regno[5]) begin
              abstract_cmd[2][31:0] =
                  dm::float_store(ac_ar.aarsize, ac_ar.regno[4:0], LoadBaseAddr, dm::DataAddr);
            end else begin
              abstract_cmd[2][31:0] =
                  dm::store(ac_ar.aarsize, ac_ar.regno[4:0], LoadBaseAddr, dm::DataAddr);
            end
          // CSR access
          end else begin
            // CSR register to data
            // store s0 in dscratch
            abstract_cmd[2][31:0]  = dm::csrw(dm::CSR_DSCRATCH0, 5'd8);
            // read value from CSR into s0
            abstract_cmd[2][63:32] = dm::csrr(dm::csr_reg_t'(ac_ar.regno[11:0]), 5'd8);
            // and store s0 into data section
            abstract_cmd[3][31:0]  = dm::store(ac_ar.aarsize, 5'd8, LoadBaseAddr, dm::DataAddr);
            // restore s0 again from dscratch
            abstract_cmd[3][63:32] = dm::csrr(dm::CSR_DSCRATCH0, 5'd8);
          end
        end else if (32'(ac_ar.aarsize) >= MaxAar || ac_ar.aarpostincrement == 1'b1) begin
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

  // Depending on whether the debug module is located
  // at the zero page we can instantiate a simplified version
  // which only requires one scratch register per hart.
  // For all other cases we need to set aside
  // two registers per hart, hence we also need
  // two scratch registers.
  if (HasSndScratch) begin : gen_rom_snd_scratch
    debug_rom i_debug_rom (
      .clk_i,
      .req_i,
      .addr_i  ( rom_addr  ),
      .rdata_o ( rom_rdata )
    );
  end else begin : gen_rom_one_scratch
    // It uses the zero register (`x0`) as the base
    // for its loads. The zero register does not need to
    // be saved.
    debug_rom_one_scratch i_debug_rom (
      .clk_i,
      .req_i,
      .addr_i  ( rom_addr  ),
      .rdata_o ( rom_rdata )
    );
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
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

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      halted_q   <= 1'b0;
      resuming_q <= 1'b0;
    end else begin
      halted_q   <= SelectableHarts & halted_d;
      resuming_q <= SelectableHarts & resuming_d;
    end
  end

endmodule : dm_mem
