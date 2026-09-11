// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Controller-side handling of Common Command Codes.
module i3c_controller_ccc
  import i3c_controller_pkg::*;
  import i3c_ctrl_ccc_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
#(
  parameter int unsigned DataWidth = 32
) (
  // CCC logic is enabled and active.
  // - this may be used to suppress any internal activity and gate off any output control signals
  //   when not processing CCCs.
  input                       enable_i,

  // Configuration.
  input  i3c_reg2hw_t         reg2hw_i,

  // Register state, including the CCC itself.
  // - this information is always available.
  // - write data will be reflected in the register state in the next cycle.
  input     [CtrlCRWidth-1:0] r_i[CtrlCR_Count],

  // Command state, for any additional information required.
  input  i3c_ctrl_cmd_state_t cmd_state_i,

  // Requests from the Controller FSM.
  input  i3c_ctrl_ccc_req_t   ccc_req_i,

  // Responses to the Controller FSM.
  output i3c_ctrl_ccc_rsp_t   ccc_rsp_o
);

  // The additional logic required for CCC framing in SDR modes, over and above the implementation
  // of the Transfer Command/Response Interface, is quite minimal. A Command Descriptor describes
  // a segment within the CCC framing and the Tx/Rx data is handled by the driver software.
  //
  // The most complicated CCC is the ENTDAA (Enter Dynamic Address Assignment) which is required
  // to collect the received data incrementally within an entry of the DCT before committing the
  // entry.
  //
  // Note: since the HCI does not support CCC framing in HDR modes, this logic need concern itself
  //       only with SDR traffic, i.e. bytes not 16-bit DataWords.

  import i3c_consts_pkg::*;

  // The Common Command Code, including Broadcast/Direct indication.
  // - this comes from a register but is always available, along with all of the other registers.
  i3c_ccc_e ccc;
  assign ccc = i3c_ccc_e'(r_i[CtrlCR_CCC]);

  always_comb begin
    ccc_rsp_o = '0;

    // All Common Command Codes first send the CCC itself.
    // - we handle Broadcasts with a single Defining Byte here too.
    // - for CCCs that are more involved, we append the data below after incrementing the state
    //   index.
    if (&{r_i[CtrlCR_Status][CtrlStat_SendFraming], !cmd_state_i.rep_start, ~|ccc_req_i.idx}) begin
      ccc_rsp_o.req_dvalid = 1'b1;
      ccc_rsp_o.req_type   = CReqType_SDRBytes;
      ccc_rsp_o.req_rx     = 1'b0;
      ccc_rsp_o.req_wdata  = {r_i[CtrlCR_CCC], r_i[CtrlCR_DEFB], 16'b0};
      ccc_rsp_o.req_len    = {1'b0, r_i[CtrlCR_Status][CtrlStat_HasDEFB]};
      // Advance to data transfer upon the next invocation.
      ccc_rsp_o.inc_idx = 1'b1;
    end else begin
      // Following a repeated start (Sr)
      case (r_i[CtrlCR_CCC])
        // Address Assignment command using ENTDAA.
        ENTDAA: begin  // 4.3.4.2
          case (ccc_req_i.idx)
            3'b010: begin
              // Sending the Dynamic Address must be done with Open-Drain signaling.
              ccc_rsp_o.req_dvalid = 1'b1;
              ccc_rsp_o.req_type   = CReqType_DynAddr;
              ccc_rsp_o.req_rx     = 1'b0;
              ccc_rsp_o.req_len    = 2'b00;
              // Dynamic Address, including the Parity bit supplied by the Driver.
              ccc_rsp_o.req_wdata  = {ccc_req_i.dat_entry.dynamic_address[22:16],
                                      ccc_req_i.dat_entry.dynamic_address[23], 24'b0};
              ccc_rsp_o.inc_idx    = 1'b1;
            end
            3'b011: begin
              // TODO: At this point we should be accepting/responding to ACK/NACK.
              // We must send Sr at this point, the command is continuing.
              ccc_rsp_o.done       = 1'b1;
              ccc_rsp_o.err_status = ErrStatus_OK;
            end
            default: begin
              // We can receive 4 bytes from the transceiver at a time; transfer the 8 bytes of
              // the target description as two transfers (`idx` of 000 and 001).
              ccc_rsp_o.req_dvalid = 1'b1;
              ccc_rsp_o.req_type   = CReqType_ArbDAA;
              ccc_rsp_o.req_rx     = 1'b1;
              ccc_rsp_o.req_len    = 2'b11;
              ccc_rsp_o.inc_idx    = 1'b1;
            end
          endcase
        end

        // Address Assignment command using SETDASA.
        SETDASA: begin  // 4.3.7.3.10
          case (ccc_req_i.idx)
            3'b001: begin
              // TODO: At this point we should be accepting/responding to ACK/NACK.
              // We must send Sr at this point, the command is continuing.
              // return.
              ccc_rsp_o.done       = 1'b1;
              ccc_rsp_o.err_status = ErrStatus_OK;
            end
            default: begin
              // TODO: Sending the Static and Dynamic Addresses with Open Drain signaling.
              ccc_rsp_o.req_dvalid = 1'b1;
              ccc_rsp_o.req_type   = CReqType_Address;
              ccc_rsp_o.req_rx     = 1'b0;
              ccc_rsp_o.req_len    = 2'b01;
              // Dynamic Address. SETDASA does not carry a parity bit in the LSB (4.3.7.3.10).
              ccc_rsp_o.req_wdata  = {ccc_req_i.dat_entry.static_address, 1'b0,  // RnW.
                                      ccc_req_i.dat_entry.dynamic_address[22:16], 1'b0,
                                      16'b0};
              ccc_rsp_o.inc_idx    = 1'b1;
            end
          endcase
        end

        default: begin
          // TODO: Extend this for data reception too.
          // Generic CCC handling
          // - Defining Byte, if supplied, has already been transmitted with the CCC.
          // - Here we are concerned with transmitting the data payload, if any.
          case (ccc_req_i.idx)
            // Pass Tx buffer data to the transceiver logic.
            3'b001:
              if (ccc_req_i.txd_valid) begin
                ccc_rsp_o.req_dvalid = 1'b1;
                ccc_rsp_o.req_type   = CReqType_SDRBytes;
                ccc_rsp_o.req_rx     = 1'b0;
                ccc_rsp_o.req_wdata  = ccc_req_i.txd_data;
                ccc_rsp_o.req_len    = ccc_req_i.txd_len;
                // When the request has been accepted by the transceiver,
                // we'll advance to the next state.
                ccc_rsp_o.inc_idx = 1'b1;
              end else if (ccc_req_i.txd_left) begin
                ccc_rsp_o.txd_req = 1'b1;
              end else begin
                ccc_rsp_o.done       = 1'b1;
                ccc_rsp_o.err_status = ErrStatus_OK;
              end
            //
            default: begin
              // Consume the Tx data that we just sent to the transceiver.
              ccc_rsp_o.txd_consume = 1'b1;
              // Index toggles between 1 and 2 until all data has been transmitted.
              ccc_rsp_o.rst_idx     = 1'b1;
              ccc_rsp_o.inc_idx     = 1'b1;
            end
          endcase
        end
      endcase
    end
  end

endmodule
