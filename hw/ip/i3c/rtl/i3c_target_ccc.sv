// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Target-side handling of Common Command Codes.
module i3c_target_ccc
  import i3c_consts_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
  import i3c_targ_ccc_pkg::*;
#(
  parameter int unsigned NumTargets = 2
) (
  // CCC logic is enabled and active.
  // - this may be used to suppress any internal activity and gate off any output control signals
  //   when not processing CCCs.
  input                         enable_i,

  // Configuration.
  input  i3c_reg2hw_t           reg2hw_i,

  // Register state, including the CCC itself.
  // - this information is always available.
  // - write data will be reflected in the register state in the next cycle.
  input       [TargCRWidth-1:0] r_i[TargCR_Count],

  // Requests from Target FSM.
  input  i3c_targ_ccc_req_t     ccc_req_i,

  // Responses to Target FSM.
  output i3c_targ_ccc_rsp_t     ccc_rsp_o,

  // ----- Reading of Target information (Direct GET CCCs). -----

  // ----- Updating of Target information (Broadcast/Direct SET CCCs). -----
  output logic [NumTargets-1:0] dynaddr_de_o,
  output                        dynaddr_valid_d_o,
  output logic            [6:0] dynaddr_d_o[NumTargets],
  output       [NumTargets-1:0] mwl_de_o,
  output       [NumTargets-1:0] mrl_de_o,
  output       [NumTargets-1:0] ibi_de_o,
  output                 [15:0] mwl_d_o,
  output                 [15:0] mrl_d_o,
  output                  [7:0] ibi_d_o,
  output i3c_endis_event_t      endis_event_o,
  // Update the RSTACT in response to CCC.
  output                        rstact_de_o,
  output i3c_rstact_e           rstact_d_o,
  // Changes to group addressing.
  output                        grp_set_o,
  output                        grp_rst_o,
  output                        grp_all_o,
  output                  [6:0] grp_addr_o,
  output       [NumTargets-1:0] grp_targets_o,
  // Activity States (ENTASn).
  output       [NumTargets-1:0] act_state_de_o,
  output logic            [1:0] act_state_d_o,
  // ENDXFER Configuration.
  output       [NumTargets-1:0] endxfer_cand_de_o,
  output                  [2:0] endxfer_cand_d_o,
  output       [NumTargets-1:0] endxfer_de_o,
  output logic            [2:0] endxfer_d_o[NumTargets],
  // Test Mode (ENTTM).
  output                        test_mode_de_o,
  output                        test_mode_d_o,
  // Protocol Error (Table 27 / TARG_STATUS.PROTOCOL_ERROR).
  output                        protocol_error_de_o,
  output                        protocol_error_d_o
);

  // The Common Command Code, including Broadcast/Direct indication.
  // - this comes from a register but is always available, along with all of the other registers.
  i3c_ccc_e ccc;
  assign ccc = i3c_ccc_e'(r_i[TargCR_CCC]);
  // Defining Byte, if any.
  // - Note: this may actually be the first byte of write data from the setup segment for CCCs
  //   that do not have a Defining Byte.
  wire [7:0] defb = r_i[TargCR_DEFB];
  wire   has_defb = r_i[TargCR_Status][TargStat_HasDEFB];
  // Present the first few bytes of write data.
  wire [7:0] wdata0 = r_i[TargCR_WData0];
  wire [7:0] wdata1 = r_i[TargCR_WData1];
  wire [7:0] wdata2 = r_i[TargCR_WData2];

  // We are only combinationally supplying data from persistent register state here, but we are
  // doing this for a set of Virtual Targets so perform the decoding once to determine the source
  // of the read data that we must provide.
  typedef enum {
    RData_MWL0,
    RData_MWL1,
    RData_MRL0,
    RData_MRL1,
    RData_IBI,
    RData_PID0,
    RData_PID1,
    RData_PID2,
    RData_PID3,
    RData_PID4,
    RData_PID5,
    RData_BCR,
    RData_DCR,
    RData_GETCAP1,
    RData_GETCAP2,
    RData_GETCAP3,
    RData_GETCAP4,
    RData_TGTSTAT0,
    RData_TGTSTAT1,
    RData_PRECR0,
    RData_PRECR1,
    RData_TESTPAT0,
    RData_TESTPAT1,
    RData_TESTPAT2,
    RData_TESTPAT3,
    RData_CRCAP1,
    RData_CRCAP2,
    RData_VTCAP1,
    RData_VTCAP2,
    RData_DYNADDR,
    RData_ENDXFER,
    RData_MAXWR,
    RData_MAXRD,
    RData_MAXRDTURN0,
    RData_MAXRDTURN1,
    RData_MAXRDTURN2,
    RData_CRHDLY1,
    // Development/diagnostic aid; should never occur because the transceiver logic should
    // accept only supported CCCs.
    RData_UNDEF
  } rdata_src_e;

  // Decode the Common Command Code and the index within the read data to determine what data
  // must be presented.
  rdata_src_e rdata_src;
  always_comb begin
    rdata_src = RData_UNDEF;
    case (ccc)
      GETMWL:  // Figure 27.
        case (ccc_req_i.idx)
          0: rdata_src = RData_MWL0;
          1: rdata_src = RData_MWL1;
        endcase
      GETMRL:  // Figure 29.
        case (ccc_req_i.idx)
          0: rdata_src = RData_MRL0;
          1: rdata_src = RData_MRL1;
          2: rdata_src = RData_IBI;
        endcase
      GETPID:  // Figure 36.
        case (ccc_req_i.idx)
          0: rdata_src = RData_PID0;
          1: rdata_src = RData_PID1;
          2: rdata_src = RData_PID2;
          3: rdata_src = RData_PID3;
          4: rdata_src = RData_PID4;
          5: rdata_src = RData_PID5;
        endcase
      GETBCR: rdata_src = RData_BCR;  // Figure 37.
      GETDCR: rdata_src = RData_DCR;  // Figure 38.
      GETSTATUS:  // TODO: Check support for NASTAT SCMSTAT (Table 28).
        if (has_defb && (defb != 8'h00)) begin
          case (defb)
            8'h91:
              case (ccc_req_i.idx)
                0: rdata_src = RData_PRECR0;
                1: rdata_src = RData_PRECR1;
              endcase
          endcase
        end else begin
          case (ccc_req_i.idx)
            0: rdata_src = RData_TGTSTAT0;
            1: rdata_src = RData_TGTSTAT1;
          endcase
        end
      // TODO(31128): We have to conditionally respond with 'Not Accepted through a NACK.'
      GETACCCR: rdata_src = RData_DYNADDR;
      //
      ENDXFER:  rdata_src = RData_ENDXFER;
      GETMXDS:  // Figure 47.
        if (has_defb && (defb != 8'h00)) begin
          case (defb)
            8'h91: rdata_src = RData_CRHDLY1;
          endcase
        end else begin
          case (ccc_req_i.idx)
            0: rdata_src = RData_MAXWR;
            1: rdata_src = RData_MAXRD;
            2: rdata_src = RData_MAXRDTURN0;
            3: rdata_src = RData_MAXRDTURN1;
            4: rdata_src = RData_MAXRDTURN2;
          endcase
        end
      GETCAPS:  // Figure 50.
        if (has_defb && (defb != 8'h00)) begin
          // GETCAPS Format 2
          case (defb)
            8'h5a:
              case (ccc_req_i.idx)
                0: rdata_src = RData_TESTPAT0;
                1: rdata_src = RData_TESTPAT1;
                2: rdata_src = RData_TESTPAT2;
                3: rdata_src = RData_TESTPAT3;
              endcase
            8'h91: 
              case (ccc_req_i.idx)
                0: rdata_src = RData_CRCAP1;
                1: rdata_src = RData_CRCAP2;
              endcase
            // TODO: DEFB shall be validated in _trx.
            8'h93:
              case (ccc_req_i.idx)
                0: rdata_src = RData_VTCAP1;
                1: rdata_src = RData_VTCAP2;
              endcase
          endcase
        end else begin
          // GETCAPS Format 1
          case (ccc_req_i.idx)
            0: rdata_src = RData_GETCAP1;
            1: rdata_src = RData_GETCAP2;
            2: rdata_src = RData_GETCAP3;
            3: rdata_src = RData_GETCAP4;
          endcase
        end
      // TODO(#31128): entry for RSTACT currently missing.
      default: rdata_src = RData_UNDEF;
    endcase
  end

  // Maximum Read Turnaround Time is encoded logarithmically.
  logic [23:0] maxrdturn[NumTargets];
  logic [3:0] maxrdscale[NumTargets];
  for (genvar t = 0; t < NumTargets; t++) begin : gen_maxrd
    assign maxrdscale[t] = reg2hw_i.targ_max_rdwr[t].rdturn_scale.q;
    assign maxrdturn[t] = {reg2hw_i.targ_max_rdwr[t].rdturn_val.q, 1'b0} << maxrdscale[t];
  end

  // TODO: GETSTATUS (TGTSTAT1).
  logic [3:0] pend_interrupt;
  assign pend_interrupt = '0;

  // Activity Mode field of GETSTATUS Format 1 (Table 27): a Controller-capable Device that is
  // unable to participate in the steps to prepare for Controller Role Handoff must report 2'b11.
  logic [1:0] cr_acr_mode;
  assign cr_acr_mode = reg2hw_i.targ_addr[0].dynamic_addr_valid.q ? 2'b00 : 2'b11;

  // Supply the data for transmission and an indication of whether this is the final byte;
  // the transceiver logic shall signal this to the Controller to terminate the Read Transfer.
  //
  // Data is presented - and consumed - for all Virtual Targets simultaneously, leaving the
  // transceiver logic to decide which shall be transmitted because the clock domain crossings
  // prevent a sufficiently fast turnaround in response to the received Target address.
  //
  // One final consideration is that the RnW indicator is received even later than the Target
  // address, so we must also preemptively supply read data when it turns out that the CCC is
  // a Direct SET; for a small number of the Common Command Codes it is impossible to differentiate
  // a GET from a SET until we receive the RnW bit.
  logic [7:0] rdata[NumTargets];
  logic rlast;
  always_comb begin
    for (int unsigned t = 0; t < NumTargets; t++) begin
      case (rdata_src)
        RData_MWL0: rdata[t] = reg2hw_i.targ_rw_len[t].mwl.q[15:8];
        RData_MWL1: rdata[t] = reg2hw_i.targ_rw_len[t].mwl.q[7:0];
        RData_MRL0: rdata[t] = reg2hw_i.targ_rw_len[t].mrl.q[15:8];
        RData_MRL1: rdata[t] = reg2hw_i.targ_rw_len[t].mrl.q[7:0];
        RData_IBI:  rdata[t] = reg2hw_i.targ_ibi_len[t].q;
        RData_PID0: rdata[t] = reg2hw_i.targ_char[t].pid_hi.q[15:8];
        RData_PID1: rdata[t] = reg2hw_i.targ_char[t].pid_hi.q[7:0];
        RData_PID2: rdata[t] = reg2hw_i.targ_pid_lo[t].q[31:24];
        RData_PID3: rdata[t] = reg2hw_i.targ_pid_lo[t].q[23:16];
        RData_PID4: rdata[t] = reg2hw_i.targ_pid_lo[t].q[15:8];
        RData_PID5: rdata[t] = reg2hw_i.targ_pid_lo[t].q[7:0];
        RData_BCR:  rdata[t] = reg2hw_i.targ_char[t].bcr.q;
        RData_DCR:  rdata[t] = reg2hw_i.targ_char[t].dcr.q;
        RData_GETCAP1: rdata[t] = 8'h1;
        RData_GETCAP2: rdata[t] = 8'hf2;  // Max support, I3C Basic V1.2.
        // TODO: This is quite likely to need revising.
        RData_GETCAP3: rdata[t] = 8'h58;
        RData_GETCAP4: rdata[t] = 8'h00;
        RData_TGTSTAT0: rdata[t] = 8'h00;
        // GETSTATUS Format 1, LSB byte (Table 27). A Controller-capable Device reports its
        // readiness to participate in Controller Role Handoff via the Activity Mode field, so that
        // field is meaningful only for Virtual Target 0, which is the Standby Controller.
        RData_TGTSTAT1: begin
          rdata[t] = {(t == 0) ? cr_acr_mode : 2'b00,        // Activity Mode.
                      reg2hw_i.targ_status.protocol_error.q, // Protocol Error.
                      1'b0,                                  // Reserved.
                      pend_interrupt};                       // Pending Interrupt.
        end
        RData_PRECR0: rdata[t] = 8'h00;
        RData_PRECR1: rdata[t] = {6'b0, reg2hw_i.stby_cr_control.handoff_delay_nack.q,
                                        reg2hw_i.stby_cr_control.handoff_deep_sleep.q};
        RData_TESTPAT0,
        RData_TESTPAT2: rdata[t] = 8'ha5;
        RData_TESTPAT1,
        RData_TESTPAT3: rdata[t] = 8'h5a;
        // Hot-Join + Group Mgmt [+ Delayed Controller Handoff for VT 0] Support.
        RData_CRCAP1: rdata[t] = {4'b0000,
                                  (t == 0) ? reg2hw_i.stby_cr_control.handoff_delay_nack.q : 1'b0,
                                  3'b011}; 
        RData_CRCAP2: rdata[t] = 8'b0000_0101; // IBI and Deep Sleep capable.
        RData_VTCAP1: rdata[t] = {2'b00, reg2hw_i.targ_caps[t].vtcap1_shared_det.q,
                                         reg2hw_i.targ_caps[t].vtcap1_side_fx.q, 1'b0,
                                         reg2hw_i.targ_caps[t].vtcap1_type.q};
        RData_VTCAP2: rdata[t] = {3'b000, reg2hw_i.targ_caps[t].vtcap2_bus_ctx.q,
                                          reg2hw_i.targ_caps[t].vtcap2_addr_remap.q,
                                          reg2hw_i.targ_caps[t].vtcap2_irq.q};
        RData_DYNADDR: begin
          if (t > 0 || !reg2hw_i.targ_addr[t].dynamic_addr_valid.q) begin
            // Dynamic address is returned for GETACCCR, which is testing the suitability of the
            // Standby Controller to assume control of the bus. We therefore return an invalid
            // address for any Virtual Target incapable of assuming the role of Active Controller.
            // TODO(#31128): This must be handled in the transceiver. The 0-data here does not hurt,
            //               but the incapability must be signalled through a NACK.
            rdata[t] = 8'h00;
          end else begin
            // Figure 42: Return dynamic address and ~XOR parity of it in bit 0
            rdata[t] = {reg2hw_i.targ_addr[t].dynamic_addr.q,
                        ~(^reg2hw_i.targ_addr[t].dynamic_addr.q)};
          end
        end
        RData_ENDXFER: begin
          // TODO: DEFB has already been validated.
          if (defb == 8'hf7) begin
            rdata[t] = {!reg2hw_i.targ_info[t].endxfer_cand_crc_early.q, 1'b1,
                         reg2hw_i.targ_info[t].endxfer_cand_wr_early_term.q,
                         reg2hw_i.targ_info[t].endxfer_cand_wr_nack.q, 4'h0};
          end else begin
            rdata[t] = {!reg2hw_i.targ_info[t].endxfer_crc_early.q, 1'b1,
                         reg2hw_i.targ_info[t].endxfer_wr_early_term.q,
                         reg2hw_i.targ_info[t].endxfer_wr_nack.q, 4'h0};
          end
        end
        RData_MAXWR: rdata[t] = reg2hw_i.targ_max_rdwr[t].maxwr.q;
        RData_MAXRD: rdata[t] = reg2hw_i.targ_max_rdwr[t].maxrd.q;
        RData_MAXRDTURN0: rdata[t] = maxrdturn[t][23:16];
        RData_MAXRDTURN1: rdata[t] = maxrdturn[t][15:8];
        RData_MAXRDTURN2: rdata[t] = maxrdturn[t][7:0];
        RData_CRHDLY1: rdata[t] = {5'b0, reg2hw_i.targ_control.crhdly1_set_as.q,
                                         reg2hw_i.targ_control.crhdly1_as.q};
        // Debugging/diagnostic aid; should never occur.
        default: rdata[t] = 8'hbd;
      endcase
    end

    // Is this the final byte of read data?
    rlast = 1'b0;
    case (rdata_src)
      // Reading from these data sources signals the end of the command.
      RData_MWL1,
      RData_IBI,
      RData_PID5,
      RData_GETCAP4,
      RData_TGTSTAT1,
      RData_PRECR1,
      RData_TESTPAT3,
      RData_VTCAP2,
      RData_CRCAP2,
      RData_DYNADDR,
      RData_ENDXFER,
      RData_MAXRDTURN2,
      RData_CRHDLY1: rlast = 1'b1;

      // On MRL1, we can only continue to the IBI byte if the currently addressed target is
      // IBI capable. Watch out for group addresses.
      RData_MRL1: rlast = ccc_req_i.is_group || (ccc_req_i.targ_id >= NumTargets) ||
                          ((ccc_req_i.targ_id < NumTargets) &&
                           !reg2hw_i.targ_char[ccc_req_i.targ_id].bcr.q[2]);

      // These values are read by ENTDAA too, so termination depends upon the CCC received.
      RData_BCR: rlast = (ccc == GETBCR);
      RData_DCR: rlast = (ccc == GETDCR);

      // Debugging/diagnostic aid; should never occur, but terminate the Read Transfer rather than
      // stalling the bus with an unbounded response.
      RData_UNDEF: rlast = 1'b1;

      // All remaining data sources supply an intermediate byte of a multi-byte response, so the
      // Read Transfer must continue.
      default: rlast = 1'b0;
    endcase
  end

  // We choose to collect the data bytes from a Write Segment/Phase until it has been received
  // successfully, at which point we commit the write operation to the register state.
  logic wr_commit;

  always_comb begin
    ccc_rsp_o = '0;
    // Supply read data for transmission.
    for (int unsigned t = 0; t < NumTargets; t++) ccc_rsp_o.req_cdata[t] = rdata[t];
    ccc_rsp_o.req_clast = rlast;
    wr_commit = 1'b0;
    case (ccc_req_i.rsn)
      TargCRsn_TxD: begin
        // Return the read data selected/constructed above.
        ccc_rsp_o.req_cvalid = 1'b1; //ccc_req_i.en;
      end
      TargCRsn_RxD:
        if (ccc_req_i.sr) begin
          if (|ccc_req_i.idx) begin
            if (ccc_req_i.rnw) begin
              // Return the read data selected/constructed above.
              ccc_rsp_o.req_cvalid = ccc_req_i.en;
            end else begin
              // Collect write data into registers whilst we're still receiving it.
              ccc_rsp_o.reg_we = ccc_req_i.en;
              case (ccc_req_i.idx)
                'h1: ccc_rsp_o.reg_widx = TargCR_WData0;
                'h2: ccc_rsp_o.reg_widx = TargCR_WData1;
                'h3: ccc_rsp_o.reg_widx = TargCR_WData2;
                default: ccc_rsp_o.reg_we = 1'b0;
              endcase
              ccc_rsp_o.reg_wdata = ccc_req_i.rdata;
            end
          end else begin
            // This is the first byte received after Sr, so it's a Target/Group address.
            // - the FSM logic records in the TargCR_Status register whether it's a group address.
            ccc_rsp_o.reg_we    = ccc_req_i.en;
            ccc_rsp_o.reg_widx  = TargCR_Targets;
            ccc_rsp_o.reg_wdata = ('b1 << ccc_req_i.targ_id) | {NumTargets{ccc_req_i.is_group}};
          end
        end else begin
          // All of the data in the CCC setup is write data; capture it in registers.
          ccc_rsp_o.reg_we    = ccc_req_i.en;
          ccc_rsp_o.reg_wdata = ccc_req_i.rdata;
          case (ccc_req_i.idx)
            'h0: begin
              // Capture the CCC in a register.
              ccc_rsp_o.reg_widx = TargCR_CCC;
            end
            'h1: begin
              // Capture the Defining Byte in a dedicated register, if expected.
              ccc_rsp_o.reg_widx = ccc_has_defb(ccc) ? TargCR_DEFB : TargCR_WData0;
            end
            'h2: ccc_rsp_o.reg_widx = has_defb ? TargCR_WData0 : TargCR_WData1;
            'h3: ccc_rsp_o.reg_widx = has_defb ? TargCR_WData1 : TargCR_WData2;
            'h4: begin
              if (has_defb) ccc_rsp_o.reg_widx = TargCR_WData2;
              else ccc_rsp_o.reg_we = 1'b0;  // No WData byte left without a DEFB.
            end
            default: begin
              // Any additional data byte(s) are dropped here; targets shall ignore unexpected
              // additional data bytes.
              ccc_rsp_o.reg_we = 1'b0;
            end
          endcase
        end
      // These are single-cycle reasons, so no need to qualify with 'en'.
      TargCRsn_Sr: wr_commit = ccc_req_i.sr;
      TargCRsn_P:  wr_commit = 1'b1;
      // All cases are covered above; no requirement for a `default` clause.
    endcase
  end

  // The set of selected targets is required in many `Set` CCCs.
  wire [NumTargets-1:0] targets = r_i[TargCR_Targets][NumTargets-1:0];

  // Modification of Dynamic Address.
  // - RSTDAA, SETAASA, SETDASA, SETNEWDA.
  // TODO: ENTDAA
  assign dynaddr_valid_d_o = (ccc != RSTDAA);
  for (genvar t = 0; t < NumTargets; t++) begin : gen_dynaddr
    assign dynaddr_de_o[t] = wr_commit & r_i[TargCR_Targets][t] &
                             ((ccc inside {RSTDAA, SETDASA, SETNEWDA}) ||
                              (ccc == SETAASA && reg2hw_i.targ_addr[t].static_addr_valid.q &&
                               !reg2hw_i.targ_addr[t].dynamic_addr_valid.q));
    // SETDASA and SETNEWDA carry the address in the Dynamic Address Byte, which holds the 7-bit
    // address in Bits[7:1] with Bit[0] set to 1'b0 (Figures 33 and 35).
    assign dynaddr_d_o[t]  = (ccc == SETAASA) ?  reg2hw_i.targ_addr[t].static_addr.q : wdata0[7:1];
  end

  // Set Maximum Write/Read/IBI Length.
  // - IBI payload is optionally supplied.
  wire setmwl = wr_commit & (ccc inside {SETMWLB, SETMWL});
  wire setmrl = wr_commit & (ccc inside {SETMRLB, SETMRL});
  wire setibi = wr_commit & (ccc inside {SETMRLB, SETMRL}) & (ccc_req_i.idx == 4'd4);
  assign mwl_de_o = {NumTargets{setmwl}} & targets;
  assign mrl_de_o = {NumTargets{setmrl}} & targets;
  assign ibi_de_o = {NumTargets{setibi}} & targets;
  assign mwl_d_o  = {wdata0, wdata1};
  assign mrl_d_o  = {wdata0, wdata1};
  assign ibi_d_o  =  wdata2;

  // Enable/Disable events.
  wire enevt  = wr_commit & (ccc inside {ENECB,  ENEC});
  wire disevt = wr_commit & (ccc inside {DISECB, DISEC});
  assign endis_event_o.enint  = {NumTargets{enevt  & wdata0[0]}} & targets;
  assign endis_event_o.disint = {NumTargets{disevt & wdata0[0]}} & targets;
  assign endis_event_o.encr   = {NumTargets{enevt  & wdata0[1]}} & targets;
  assign endis_event_o.discr  = {NumTargets{disevt & wdata0[1]}} & targets;
  assign endis_event_o.enhj   = {NumTargets{enevt  & wdata0[3]}} & targets;
  assign endis_event_o.dishj  = {NumTargets{disevt & wdata0[3]}} & targets;

  // Reset Action.
  // Write only on broadcast or if any of our virtual targets has been addressed.
  // Write only if the defining byte has the MSB cleared, otherwise it is a GET RSTACT.
  assign rstact_de_o = wr_commit & (ccc inside {RSTACTB, RSTACT}) & ((ccc == RSTACTB) | |targets) &
                       !defb[7] & !ccc_req_i.rnw;
  assign rstact_d_o  = i3c_rstact_e'(defb);

  // Group addressing changes.
  assign grp_rst_o     = wr_commit & (ccc inside {RSTGRPA, RSTGRPAB, RSTDAA});
  assign grp_set_o     = wr_commit & (ccc == SETGRPA);
  // Direct RSTGRPA carries no data byte when addressed to a Target Address (Figure 60), so there is
  // no way to name a single Group to leave; per RSTDAA's analogous "reset all of its assigned Group
  // Addresses" wording, the only sensible choice is therefore to remove the addressed target(s)
  // from every group they are currently in.
  assign grp_all_o     = ccc inside {RSTGRPA, RSTGRPAB, RSTDAA};
  assign grp_addr_o    = wdata0[7:1]; // Bit 0 is a fixed 1'b0 filler (Figure 59).
  assign grp_targets_o = targets;

  // Activity State of I3C bus (Table 21).
  // - both the Broadcast (ENTASnB) and Direct (ENTASn) forms shall be actioned.
  assign act_state_de_o = {NumTargets{wr_commit &
                                     (ccc inside {ENTAS0,  ENTAS1,  ENTAS2,  ENTAS3,
                                                  ENTAS0B, ENTAS1B, ENTAS2B, ENTAS3B})}} & targets;
  always_comb begin
    case (ccc)
      ENTAS3, ENTAS3B: act_state_d_o = 2'b11;  // 50ms: Lowest-activity operation.
      ENTAS2, ENTAS2B: act_state_d_o = 2'b10;  // 2ms.
      ENTAS1, ENTAS1B: act_state_d_o = 2'b01;  // 100us.
      default:         act_state_d_o = 2'b00;  // Latency-free operation.
    endcase
  end

  // Candidate ENDXFER Configuration (Table 84).
  wire endxfer_set = wr_commit && (ccc inside {ENDXFER, ENDXFERB}) && (defb == 8'hf7);
  assign endxfer_cand_de_o = {NumTargets{endxfer_set}} & targets;
  assign endxfer_cand_d_o  = {wdata0[7:6] == 2'b01, wdata0[5], wdata0[4]};
  // Activated ENDXFER Configuration (Table 84).
  wire endxfer_commit = &{wr_commit, ccc inside {ENDXFER, ENDXFERB},
                          defb == 8'haa, wdata0 == 8'haa};
  assign endxfer_de_o =  {NumTargets{endxfer_commit}} & targets;
  for (genvar t = 0; t < NumTargets; t++) begin : gen_vt_endxfer
    assign endxfer_d_o[t] = {reg2hw_i.targ_info[t].endxfer_cand_crc_early.q,
                             reg2hw_i.targ_info[t].endxfer_cand_wr_early_term.q,
                             reg2hw_i.targ_info[t].endxfer_cand_wr_nack.q};
  end

  // Test Mode.
  assign test_mode_de_o = wr_commit & (ccc == ENTTM) & (defb inside {8'h00, 8'h01});
  assign test_mode_d_o  = (defb == 8'h01);

  // Protocol Error clears when the status byte carrying it has actually been read; `RData_TGTSTAT1`
  // is unconditionally the terminal byte of a no-DEFB GETSTATUS response.
  assign protocol_error_de_o = ccc_req_i.en && (ccc_req_i.rsn == TargCRsn_TxD) &&
                               (rdata_src == RData_TGTSTAT1);
  assign protocol_error_d_o  = 1'b0;  // Only ever clears from here.

endmodule
