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
 * File:  dm_csrs.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2018
 *
 * Description: Debug CSRs. Communication over Debug Transport Module (DTM)
 */

module dm_csrs #(
  parameter int unsigned        NrHarts          = 1,
  parameter int unsigned        BusWidth         = 32,
  parameter logic [NrHarts-1:0] SelectableHarts  = {NrHarts{1'b1}}
) (
  input  logic                              clk_i,           // Clock
  input  logic                              rst_ni,          // Asynchronous reset active low
  input  logic                              testmode_i,
  input  logic                              dmi_rst_ni,      // sync. DTM reset,
                                                             // active-low
  input  logic                              dmi_req_valid_i,
  output logic                              dmi_req_ready_o,
  input  dm::dmi_req_t                      dmi_req_i,
  // every request needs a response one cycle later
  output logic                              dmi_resp_valid_o,
  input  logic                              dmi_resp_ready_i,
  output dm::dmi_resp_t                     dmi_resp_o,
  // global ctrl
  output logic                              ndmreset_o,      // non-debug module reset active-high
  output logic                              dmactive_o,      // 1 -> debug-module is active,
                                                             // 0 -> synchronous re-set
  // hart status
  input  dm::hartinfo_t [NrHarts-1:0]       hartinfo_i,      // static hartinfo
  input  logic [NrHarts-1:0]                halted_i,        // hart is halted
  input  logic [NrHarts-1:0]                unavailable_i,   // e.g.: powered down
  input  logic [NrHarts-1:0]                resumeack_i,     // hart acknowledged resume request
  // hart control
  output logic [19:0]                       hartsel_o,       // hartselect to ctrl module
  output logic [NrHarts-1:0]                haltreq_o,       // request to halt a hart
  output logic [NrHarts-1:0]                resumereq_o,     // request hart to resume
  output logic                              clear_resumeack_o,

  output logic                              cmd_valid_o,       // debugger writing to cmd field
  output dm::command_t                      cmd_o,             // abstract command
  input  logic                              cmderror_valid_i,  // an error occurred
  input  dm::cmderr_e                       cmderror_i,        // this error occurred
  input  logic                              cmdbusy_i,         // cmd is currently busy executing

  output logic [dm::ProgBufSize-1:0][31:0]  progbuf_o, // to system bus
  output logic [dm::DataCount-1:0][31:0]    data_o,

  input  logic [dm::DataCount-1:0][31:0]    data_i,
  input  logic                              data_valid_i,
  // system bus access module (SBA)
  output logic [BusWidth-1:0]               sbaddress_o,
  input  logic [BusWidth-1:0]               sbaddress_i,
  output logic                              sbaddress_write_valid_o,
  // control signals in
  output logic                              sbreadonaddr_o,
  output logic                              sbautoincrement_o,
  output logic [2:0]                        sbaccess_o,
  // data out
  output logic                              sbreadondata_o,
  output logic [BusWidth-1:0]               sbdata_o,
  output logic                              sbdata_read_valid_o,
  output logic                              sbdata_write_valid_o,
  // read data in
  input  logic [BusWidth-1:0]               sbdata_i,
  input  logic                              sbdata_valid_i,
  // control signals
  input  logic                              sbbusy_i,
  input  logic                              sberror_valid_i, // bus error occurred
  input  logic [2:0]                        sberror_i // bus error occurred
);

  // the amount of bits we need to represent all harts
  localparam int unsigned HartSelLen = (NrHarts == 1) ? 1 : $clog2(NrHarts);
  localparam int unsigned NrHartsAligned = 2**HartSelLen;

  dm::dtm_op_e dtm_op;
  assign dtm_op = dm::dtm_op_e'(dmi_req_i.op);


  localparam dm::dm_csr_e DataEnd = dm::dm_csr_e'(dm::Data0 + {4'h0, dm::DataCount} - 8'h1);
  localparam dm::dm_csr_e ProgBufEnd = dm::dm_csr_e'(dm::ProgBuf0 + {4'h0, dm::ProgBufSize} - 8'h1);

  logic [31:0] haltsum0, haltsum1, haltsum2, haltsum3;
  logic [((NrHarts-1)/2**5 + 1) * 32 - 1 : 0] halted;
  logic [(NrHarts-1)/2**5:0][31:0] halted_reshaped0;
  logic [(NrHarts-1)/2**10:0][31:0] halted_reshaped1;
  logic [(NrHarts-1)/2**15:0][31:0] halted_reshaped2;
  logic [((NrHarts-1)/2**10+1)*32-1:0] halted_flat1;
  logic [((NrHarts-1)/2**15+1)*32-1:0] halted_flat2;
  logic [31:0] halted_flat3;

  // haltsum0
  logic [14:0] hartsel_idx0;
  always_comb begin : p_haltsum0
    halted              = '0;
    haltsum0            = '0;
    hartsel_idx0        = hartsel_o[19:5];
    halted[NrHarts-1:0] = halted_i;
    halted_reshaped0    = halted;
    if (hartsel_idx0 < 15'((NrHarts-1)/2**5+1)) begin
      haltsum0 = halted_reshaped0[hartsel_idx0];
    end
  end

  // haltsum1
  logic [9:0] hartsel_idx1;
  always_comb begin : p_reduction1
    halted_flat1 = '0;
    haltsum1     = '0;
    hartsel_idx1 = hartsel_o[19:10];

    for (int unsigned k = 0; k < (NrHarts-1)/2**5+1; k++) begin
      halted_flat1[k] = |halted_reshaped0[k];
    end
    halted_reshaped1 = halted_flat1;

    if (hartsel_idx1 < 10'(((NrHarts-1)/2**10+1))) begin
      haltsum1 = halted_reshaped1[hartsel_idx1];
    end
  end

  // haltsum2
  logic [4:0] hartsel_idx2;
  always_comb begin : p_reduction2
    halted_flat2 = '0;
    haltsum2     = '0;
    hartsel_idx2 = hartsel_o[19:15];

    for (int unsigned k = 0; k < (NrHarts-1)/2**10+1; k++) begin
      halted_flat2[k] = |halted_reshaped1[k];
    end
    halted_reshaped2 = halted_flat2;

    if (hartsel_idx2 < 5'(((NrHarts-1)/2**15+1))) begin
      haltsum2         = halted_reshaped2[hartsel_idx2];
    end
  end

  // haltsum3
  always_comb begin : p_reduction3
    halted_flat3 = '0;
    for (int unsigned k = 0; k < NrHarts/2**15+1; k++) begin
      halted_flat3[k] = |halted_reshaped2[k];
    end
    haltsum3 = halted_flat3;
  end


  dm::dmstatus_t      dmstatus;
  dm::dmcontrol_t     dmcontrol_d, dmcontrol_q;
  dm::abstractcs_t    abstractcs;
  dm::cmderr_e        cmderr_d, cmderr_q;
  dm::command_t       command_d, command_q;
  logic               cmd_valid_d, cmd_valid_q;
  dm::abstractauto_t  abstractauto_d, abstractauto_q;
  dm::sbcs_t          sbcs_d, sbcs_q;
  logic [63:0]        sbaddr_d, sbaddr_q;
  logic [63:0]        sbdata_d, sbdata_q;

  logic [NrHarts-1:0] havereset_d, havereset_q;
  // program buffer
  logic [dm::ProgBufSize-1:0][31:0] progbuf_d, progbuf_q;
  logic [dm::DataCount-1:0][31:0] data_d, data_q;

  logic [HartSelLen-1:0] selected_hart;

  dm::dmi_resp_t resp_queue_inp;

  // SBA
  assign sbautoincrement_o = sbcs_q.sbautoincrement;
  assign sbreadonaddr_o    = sbcs_q.sbreadonaddr;
  assign sbreadondata_o    = sbcs_q.sbreadondata;
  assign sbaccess_o        = sbcs_q.sbaccess;
  assign sbdata_o          = sbdata_q[BusWidth-1:0];
  assign sbaddress_o       = sbaddr_q[BusWidth-1:0];

  assign hartsel_o         = {dmcontrol_q.hartselhi, dmcontrol_q.hartsello};

  // needed to avoid lint warnings
  logic [NrHartsAligned-1:0] havereset_d_aligned, havereset_q_aligned,
                             resumeack_aligned, unavailable_aligned,
                             halted_aligned;
  assign resumeack_aligned   = NrHartsAligned'(resumeack_i);
  assign unavailable_aligned = NrHartsAligned'(unavailable_i);
  assign halted_aligned      = NrHartsAligned'(halted_i);

  assign havereset_d         = NrHarts'(havereset_d_aligned);
  assign havereset_q_aligned = NrHartsAligned'(havereset_q);

  dm::hartinfo_t [NrHartsAligned-1:0] hartinfo_aligned;
  always_comb begin : p_hartinfo_align
    hartinfo_aligned = '0;
    hartinfo_aligned[NrHarts-1:0] = hartinfo_i;
  end

  // helper variables
  dm::dm_csr_e dm_csr_addr;
  dm::sbcs_t sbcs;
  dm::abstractcs_t a_abstractcs;
  logic [3:0] autoexecdata_idx; // 0 == Data0 ... 11 == Data11

  // Get the data index, i.e. 0 for dm::Data0 up to 11 for dm::Data11
  assign dm_csr_addr = dm::dm_csr_e'({1'b0, dmi_req_i.addr});
  // Xilinx Vivado 2020.1 does not allow subtraction of two enums; do the subtraction with logic
  // types instead.
  assign autoexecdata_idx = 4'({dm_csr_addr} - {dm::Data0});

  always_comb begin : csr_read_write
    // --------------------
    // Static Values (R/O)
    // --------------------
    // dmstatus
    dmstatus    = '0;
    dmstatus.version = dm::DbgVersion013;
    // no authentication implemented
    dmstatus.authenticated = 1'b1;
    // we do not support halt-on-reset sequence
    dmstatus.hasresethaltreq = 1'b0;
    // TODO(zarubaf) things need to change here if we implement the array mask
    dmstatus.allhavereset = havereset_q_aligned[selected_hart];
    dmstatus.anyhavereset = havereset_q_aligned[selected_hart];

    dmstatus.allresumeack = resumeack_aligned[selected_hart];
    dmstatus.anyresumeack = resumeack_aligned[selected_hart];

    dmstatus.allunavail   = unavailable_aligned[selected_hart];
    dmstatus.anyunavail   = unavailable_aligned[selected_hart];

    // as soon as we are out of the legal Hart region tell the debugger
    // that there are only non-existent harts
    dmstatus.allnonexistent = logic'(32'(hartsel_o) > (NrHarts - 1));
    dmstatus.anynonexistent = logic'(32'(hartsel_o) > (NrHarts - 1));

    // We are not allowed to be in multiple states at once. This is a to
    // make the running/halted and unavailable states exclusive.
    dmstatus.allhalted    = halted_aligned[selected_hart] & ~unavailable_aligned[selected_hart];
    dmstatus.anyhalted    = halted_aligned[selected_hart] & ~unavailable_aligned[selected_hart];

    dmstatus.allrunning   = ~halted_aligned[selected_hart] & ~unavailable_aligned[selected_hart];
    dmstatus.anyrunning   = ~halted_aligned[selected_hart] & ~unavailable_aligned[selected_hart];

    // abstractcs
    abstractcs = '0;
    abstractcs.datacount = dm::DataCount;
    abstractcs.progbufsize = dm::ProgBufSize;
    abstractcs.busy = cmdbusy_i;
    abstractcs.cmderr = cmderr_q;

    // abstractautoexec
    abstractauto_d = abstractauto_q;
    abstractauto_d.zero0 = '0;

    // default assignments
    havereset_d_aligned = NrHartsAligned'(havereset_q);
    dmcontrol_d         = dmcontrol_q;
    cmderr_d            = cmderr_q;
    command_d           = command_q;
    progbuf_d           = progbuf_q;
    data_d              = data_q;
    sbcs_d              = sbcs_q;
    sbaddr_d            = 64'(sbaddress_i);
    sbdata_d            = sbdata_q;

    resp_queue_inp.data     = 32'h0;
    resp_queue_inp.resp     = dm::DTM_SUCCESS;
    cmd_valid_d             = 1'b0;
    sbaddress_write_valid_o = 1'b0;
    sbdata_read_valid_o     = 1'b0;
    sbdata_write_valid_o    = 1'b0;
    clear_resumeack_o       = 1'b0;

    // helper variables
    sbcs         = '0;
    a_abstractcs = '0;

    // reads
    if (dmi_req_ready_o && dmi_req_valid_i && dtm_op == dm::DTM_READ) begin
      unique case (dm_csr_addr) inside
        [(dm::Data0):DataEnd]: begin
          resp_queue_inp.data = data_q[$clog2(dm::DataCount)'(autoexecdata_idx)];
          if (!cmdbusy_i) begin
            // check whether we need to re-execute the command (just give a cmd_valid)
            cmd_valid_d = abstractauto_q.autoexecdata[autoexecdata_idx];
          // An abstract command was executing while one of the data registers was read
          end else begin
            resp_queue_inp.resp = dm::DTM_BUSY;
            if (cmderr_q == dm::CmdErrNone) begin
              cmderr_d = dm::CmdErrBusy;
            end
          end
        end
        dm::DMControl:    resp_queue_inp.data = dmcontrol_q;
        dm::DMStatus:     resp_queue_inp.data = dmstatus;
        dm::Hartinfo:     resp_queue_inp.data = hartinfo_aligned[selected_hart];
        dm::AbstractCS:   resp_queue_inp.data = abstractcs;
        dm::AbstractAuto: resp_queue_inp.data = abstractauto_q;
        // command is read-only
        dm::Command:    resp_queue_inp.data = '0;
        [(dm::ProgBuf0):ProgBufEnd]: begin
          resp_queue_inp.data = progbuf_q[dmi_req_i.addr[$clog2(dm::ProgBufSize)-1:0]];
          if (!cmdbusy_i) begin
            // check whether we need to re-execute the command (just give a cmd_valid)
            // range of autoexecprogbuf is 31:16
            cmd_valid_d = abstractauto_q.autoexecprogbuf[{1'b1, dmi_req_i.addr[3:0]}];

          // An abstract command was executing while one of the progbuf registers was read
          end else begin
            resp_queue_inp.resp = dm::DTM_BUSY;
            if (cmderr_q == dm::CmdErrNone) begin
              cmderr_d = dm::CmdErrBusy;
            end
          end
        end
        dm::HaltSum0: resp_queue_inp.data = haltsum0;
        dm::HaltSum1: resp_queue_inp.data = haltsum1;
        dm::HaltSum2: resp_queue_inp.data = haltsum2;
        dm::HaltSum3: resp_queue_inp.data = haltsum3;
        dm::SBCS: begin
          resp_queue_inp.data = sbcs_q;
        end
        dm::SBAddress0: begin
          resp_queue_inp.data = sbaddr_q[31:0];
        end
        dm::SBAddress1: begin
          resp_queue_inp.data = sbaddr_q[63:32];
        end
        dm::SBData0: begin
          // access while the SBA was busy
          if (sbbusy_i || sbcs_q.sbbusyerror) begin
            sbcs_d.sbbusyerror = 1'b1;
            resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            sbdata_read_valid_o = (sbcs_q.sberror == '0);
            resp_queue_inp.data = sbdata_q[31:0];
          end
        end
        dm::SBData1: begin
          // access while the SBA was busy
          if (sbbusy_i || sbcs_q.sbbusyerror) begin
            sbcs_d.sbbusyerror = 1'b1;
            resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            resp_queue_inp.data = sbdata_q[63:32];
          end
        end
        default:;
      endcase
    end

    // write
    if (dmi_req_ready_o && dmi_req_valid_i && dtm_op == dm::DTM_WRITE) begin
      unique case (dm_csr_addr) inside
        [(dm::Data0):DataEnd]: begin
          if (dm::DataCount > 0) begin
            // attempts to write them while busy is set does not change their value
            if (!cmdbusy_i) begin
              data_d[dmi_req_i.addr[$clog2(dm::DataCount)-1:0]] = dmi_req_i.data;
              // check whether we need to re-execute the command (just give a cmd_valid)
              cmd_valid_d = abstractauto_q.autoexecdata[autoexecdata_idx];
            //An abstract command was executing while one of the data registers was written
            end else begin
              resp_queue_inp.resp = dm::DTM_BUSY;
              if (cmderr_q == dm::CmdErrNone) begin
                cmderr_d = dm::CmdErrBusy;
              end
            end
          end
        end
        dm::DMControl: begin
          dmcontrol_d = dmi_req_i.data;
          // clear the havreset of the selected hart
          if (dmcontrol_d.ackhavereset) begin
            havereset_d_aligned[selected_hart] = 1'b0;
          end
        end
        dm::DMStatus:; // write are ignored to R/O register
        dm::Hartinfo:; // hartinfo is R/O
        // only command error is write-able
        dm::AbstractCS: begin // W1C
          // Gets set if an abstract command fails. The bits in this
          // field remain set until they are cleared by writing 1 to
          // them. No abstract command is started until the value is
          // reset to 0.
          a_abstractcs = dm::abstractcs_t'(dmi_req_i.data);
          // reads during abstract command execution are not allowed
          if (!cmdbusy_i) begin
            cmderr_d = dm::cmderr_e'(~a_abstractcs.cmderr & cmderr_q);
          end else begin
            resp_queue_inp.resp = dm::DTM_BUSY;
            if (cmderr_q == dm::CmdErrNone) begin
              cmderr_d = dm::CmdErrBusy;
            end
          end
        end
        dm::Command: begin
          // writes are ignored if a command is already busy
          if (!cmdbusy_i) begin
            cmd_valid_d = 1'b1;
            command_d = dm::command_t'(dmi_req_i.data);
          // if there was an attempted to write during a busy execution
          // and the cmderror field is zero set the busy error
          end else begin
            resp_queue_inp.resp = dm::DTM_BUSY;
            if (cmderr_q == dm::CmdErrNone) begin
              cmderr_d = dm::CmdErrBusy;
            end
          end
        end
        dm::AbstractAuto: begin
          // this field can only be written legally when there is no command executing
          if (!cmdbusy_i) begin
            abstractauto_d                 = 32'h0;
            abstractauto_d.autoexecdata    = 12'(dmi_req_i.data[dm::DataCount-1:0]);
            abstractauto_d.autoexecprogbuf = 16'(dmi_req_i.data[dm::ProgBufSize-1+16:16]);
          end else begin
            resp_queue_inp.resp = dm::DTM_BUSY;
            if (cmderr_q == dm::CmdErrNone) begin
              cmderr_d = dm::CmdErrBusy;
            end
          end
        end
        [(dm::ProgBuf0):ProgBufEnd]: begin
          // attempts to write them while busy is set does not change their value
          if (!cmdbusy_i) begin
            progbuf_d[dmi_req_i.addr[$clog2(dm::ProgBufSize)-1:0]] = dmi_req_i.data;
            // check whether we need to re-execute the command (just give a cmd_valid)
            // this should probably throw an error if executed during another command
            // was busy
            // range of autoexecprogbuf is 31:16
            cmd_valid_d = abstractauto_q.autoexecprogbuf[{1'b1, dmi_req_i.addr[3:0]}];
          //An abstract command was executing while one of the progbuf registers was written
          end else begin
            resp_queue_inp.resp = dm::DTM_BUSY;
            if (cmderr_q == dm::CmdErrNone) begin
              cmderr_d = dm::CmdErrBusy;
            end
          end
        end
        dm::SBCS: begin
          // access while the SBA was busy
          if (sbbusy_i) begin
            sbcs_d.sbbusyerror = 1'b1;
            resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            sbcs = dm::sbcs_t'(dmi_req_i.data);
            sbcs_d = sbcs;
            // R/W1C
            sbcs_d.sbbusyerror = sbcs_q.sbbusyerror & (~sbcs.sbbusyerror);
            sbcs_d.sberror     = sbcs_q.sberror     & {3{~(sbcs.sberror == 3'd1)}};
          end
        end
        dm::SBAddress0: begin
          // access while the SBA was busy
          if (sbbusy_i || sbcs_q.sbbusyerror) begin
            sbcs_d.sbbusyerror = 1'b1;
            resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            sbaddr_d[31:0] = dmi_req_i.data;
            sbaddress_write_valid_o = (sbcs_q.sberror == '0);
          end
        end
        dm::SBAddress1: begin
          // access while the SBA was busy
          if (sbbusy_i || sbcs_q.sbbusyerror) begin
            sbcs_d.sbbusyerror = 1'b1;
            resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            sbaddr_d[63:32] = dmi_req_i.data;
          end
        end
        dm::SBData0: begin
          // access while the SBA was busy
          if (sbbusy_i || sbcs_q.sbbusyerror) begin
           sbcs_d.sbbusyerror = 1'b1;
           resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            sbdata_d[31:0] = dmi_req_i.data;
            sbdata_write_valid_o = (sbcs_q.sberror == '0);
          end
        end
        dm::SBData1: begin
          // access while the SBA was busy
          if (sbbusy_i || sbcs_q.sbbusyerror) begin
           sbcs_d.sbbusyerror = 1'b1;
           resp_queue_inp.resp = dm::DTM_BUSY;
          end else begin
            sbdata_d[63:32] = dmi_req_i.data;
          end
        end
        default:;
      endcase
    end
    // hart threw a command error and has precedence over bus writes
    if (cmderror_valid_i) begin
      cmderr_d = cmderror_i;
    end

    // update data registers
    if (data_valid_i) begin
      data_d = data_i;
    end

    // set the havereset flag when we did a ndmreset
    if (ndmreset_o) begin
      havereset_d_aligned[NrHarts-1:0] = '1;
    end
    // -------------
    // System Bus
    // -------------
    // set bus error
    if (sberror_valid_i) begin
      sbcs_d.sberror = sberror_i;
    end
    // update read data
    if (sbdata_valid_i) begin
      sbdata_d = 64'(sbdata_i);
    end

    // dmcontrol
    // TODO(zarubaf) we currently do not implement the hartarry mask
    dmcontrol_d.hasel           = 1'b0;
    // we do not support resetting an individual hart
    dmcontrol_d.hartreset       = 1'b0;
    dmcontrol_d.setresethaltreq = 1'b0;
    dmcontrol_d.clrresethaltreq = 1'b0;
    dmcontrol_d.zero1           = '0;
    dmcontrol_d.zero0           = '0;
    // Non-writeable, clear only
    dmcontrol_d.ackhavereset    = 1'b0;
    if (!dmcontrol_q.resumereq && dmcontrol_d.resumereq) begin
      clear_resumeack_o = 1'b1;
    end
    if (dmcontrol_q.resumereq && resumeack_i) begin
      dmcontrol_d.resumereq = 1'b0;
    end
    // static values for dcsr
    sbcs_d.sbversion            = 3'd1;
    sbcs_d.sbbusy               = sbbusy_i;
    sbcs_d.sbasize              = $bits(sbcs_d.sbasize)'(BusWidth);
    sbcs_d.sbaccess128          = logic'(BusWidth >= 32'd128);
    sbcs_d.sbaccess64           = logic'(BusWidth >= 32'd64);
    sbcs_d.sbaccess32           = logic'(BusWidth >= 32'd32);
    sbcs_d.sbaccess16           = logic'(BusWidth >= 32'd16);
    sbcs_d.sbaccess8            = logic'(BusWidth >= 32'd8);
  end

  // output multiplexer
  always_comb begin : p_outmux
    selected_hart = hartsel_o[HartSelLen-1:0];
    // default assignment
    haltreq_o = '0;
    resumereq_o = '0;
    if (selected_hart <= HartSelLen'(NrHarts-1)) begin
      haltreq_o[selected_hart]   = dmcontrol_q.haltreq;
      resumereq_o[selected_hart] = dmcontrol_q.resumereq;
    end
  end

  assign dmactive_o  = dmcontrol_q.dmactive;
  assign cmd_o       = command_q;
  assign cmd_valid_o = cmd_valid_q;
  assign progbuf_o   = progbuf_q;
  assign data_o      = data_q;

  assign ndmreset_o = dmcontrol_q.ndmreset;

  logic unused_testmode;
  assign unused_testmode = testmode_i;

  // response FIFO
  prim_fifo_sync #(
    .Width   ($bits(dmi_resp_o)),
    .Pass    (1'b0),
    .Depth   (2)
  ) i_fifo (
    .clk_i   ( clk_i                ),
    .rst_ni  ( dmi_rst_ni           ), // reset only when system is re-set
    .clr_i   ( 1'b0                 ),
    .wdata_i ( resp_queue_inp       ),
    .wvalid_i( dmi_req_valid_i      ),
    .wready_o( dmi_req_ready_o      ),
    .rdata_o ( dmi_resp_o           ),
    .rvalid_o( dmi_resp_valid_o     ),
    .rready_i( dmi_resp_ready_i     ),
    .full_o  (                      ), // Unused
    .depth_o (                      ), // Unused
    .err_o   (                      )  // Unused
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    // PoR
    if (!rst_ni) begin
      dmcontrol_q    <= '0;
      // this is the only write-able bit during reset
      cmderr_q       <= dm::CmdErrNone;
      command_q      <= '0;
      cmd_valid_q    <= '0;
      abstractauto_q <= '0;
      progbuf_q      <= '0;
      data_q         <= '0;
      sbcs_q         <= '{default: '0,  sbaccess: 3'd2};
      sbaddr_q       <= '0;
      sbdata_q       <= '0;
      havereset_q    <= '1;
    end else begin
      havereset_q    <= SelectableHarts & havereset_d;
      // synchronous re-set of debug module, active-low, except for dmactive
      if (!dmcontrol_q.dmactive) begin
        dmcontrol_q.haltreq          <= '0;
        dmcontrol_q.resumereq        <= '0;
        dmcontrol_q.hartreset        <= '0;
        dmcontrol_q.ackhavereset     <= '0;
        dmcontrol_q.zero1            <= '0;
        dmcontrol_q.hasel            <= '0;
        dmcontrol_q.hartsello        <= '0;
        dmcontrol_q.hartselhi        <= '0;
        dmcontrol_q.zero0            <= '0;
        dmcontrol_q.setresethaltreq  <= '0;
        dmcontrol_q.clrresethaltreq  <= '0;
        dmcontrol_q.ndmreset         <= '0;
        // this is the only write-able bit during reset
        dmcontrol_q.dmactive         <= dmcontrol_d.dmactive;
        cmderr_q                     <= dm::CmdErrNone;
        command_q                    <= '0;
        cmd_valid_q                  <= '0;
        abstractauto_q               <= '0;
        progbuf_q                    <= '0;
        data_q                       <= '0;
        sbcs_q                       <= '{default: '0,  sbaccess: 3'd2};
        sbaddr_q                     <= '0;
        sbdata_q                     <= '0;
      end else begin
        dmcontrol_q                  <= dmcontrol_d;
        cmderr_q                     <= cmderr_d;
        command_q                    <= command_d;
        cmd_valid_q                  <= cmd_valid_d;
        abstractauto_q               <= abstractauto_d;
        progbuf_q                    <= progbuf_d;
        data_q                       <= data_d;
        sbcs_q                       <= sbcs_d;
        sbaddr_q                     <= sbaddr_d;
        sbdata_q                     <= sbdata_d;
      end
    end
  end

endmodule : dm_csrs
