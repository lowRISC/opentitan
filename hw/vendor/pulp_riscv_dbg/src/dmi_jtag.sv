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
* File:   axi_riscv_debug_module.sv
* Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
* Date:   19.7.2018
*
* Description: JTAG DMI (debug module interface)
*
*/

module dmi_jtag #(
  parameter logic [31:0] IdcodeValue = 32'h00000001
) (
  input  logic         clk_i,      // DMI Clock
  input  logic         rst_ni,     // Asynchronous reset active low
  input  logic         testmode_i,

  output logic         dmi_rst_no, // hard reset
  output dm::dmi_req_t dmi_req_o,
  output logic         dmi_req_valid_o,
  input  logic         dmi_req_ready_i,

  input dm::dmi_resp_t dmi_resp_i,
  output logic         dmi_resp_ready_o,
  input  logic         dmi_resp_valid_i,

  input  logic         tck_i,    // JTAG test clock pad
  input  logic         tms_i,    // JTAG test mode select pad
  input  logic         trst_ni,  // JTAG test reset pad
  input  logic         td_i,     // JTAG test data input pad
  output logic         td_o,     // JTAG test data output pad
  output logic         tdo_oe_o  // Data out output enable
);
  assign       dmi_rst_no = rst_ni;

  logic        test_logic_reset;
  logic        shift_dr;
  logic        update_dr;
  logic        capture_dr;
  logic        dmi_access;
  logic        dtmcs_select;
  logic        dmi_reset;
  logic        dmi_tdi;
  logic        dmi_tdo;

  dm::dmi_req_t  dmi_req;
  logic          dmi_req_ready;
  logic          dmi_req_valid;

  dm::dmi_resp_t dmi_resp;
  logic          dmi_resp_valid;
  logic          dmi_resp_ready;

  typedef struct packed {
    logic [6:0]  address;
    logic [31:0] data;
    logic [1:0]  op;
  } dmi_t;

  typedef enum logic [1:0] {
    DMINoError = 2'h0, DMIReservedError = 2'h1,
    DMIOPFailed = 2'h2, DMIBusy = 2'h3
  } dmi_error_e;

  typedef enum logic [2:0] { Idle, Read, WaitReadValid, Write, WaitWriteValid } state_e;
  state_e state_d, state_q;

  logic [$bits(dmi_t)-1:0] dr_d, dr_q;
  logic [6:0] address_d, address_q;
  logic [31:0] data_d, data_q;

  dmi_t  dmi;
  assign dmi          = dmi_t'(dr_q);
  assign dmi_req.addr = address_q;
  assign dmi_req.data = data_q;
  assign dmi_req.op   = (state_q == Write) ? dm::DTM_WRITE : dm::DTM_READ;
  // we'will always be ready to accept the data we requested
  assign dmi_resp_ready = 1'b1;

  logic error_dmi_busy;
  dmi_error_e error_d, error_q;

  always_comb begin : p_fsm
    error_dmi_busy = 1'b0;
    // default assignments
    state_d   = state_q;
    address_d = address_q;
    data_d    = data_q;
    error_d   = error_q;

    dmi_req_valid = 1'b0;

    unique case (state_q)
      Idle: begin
        // make sure that no error is sticky
        if (dmi_access && update_dr && (error_q == DMINoError)) begin
          // save address and value
          address_d = dmi.address;
          data_d = dmi.data;
          if (dm::dtm_op_e'(dmi.op) == dm::DTM_READ) begin
            state_d = Read;
          end else if (dm::dtm_op_e'(dmi.op) == dm::DTM_WRITE) begin
            state_d = Write;
          end
          // else this is a nop and we can stay here
        end
      end

      Read: begin
        dmi_req_valid = 1'b1;
        if (dmi_req_ready) begin
          state_d = WaitReadValid;
        end
      end

      WaitReadValid: begin
        // load data into register and shift out
        if (dmi_resp_valid) begin
          data_d = dmi_resp.data;
          state_d = Idle;
        end
      end

      Write: begin
        dmi_req_valid = 1'b1;
        // request sent, wait for response before going back to idle
        if (dmi_req_ready) begin
          state_d = WaitWriteValid;
        end
      end

      WaitWriteValid: begin
        // got a valid answer go back to idle
        if (dmi_resp_valid) begin
          state_d = Idle;
        end
      end

      default: begin
        // just wait for idle here
        if (dmi_resp_valid) begin
          state_d = Idle;
        end
      end
    endcase

    // update_dr means we got another request but we didn't finish
    // the one in progress, this state is sticky
    if (update_dr && state_q != Idle) begin
      error_dmi_busy = 1'b1;
    end

    // if capture_dr goes high while we are in the read state
    // or in the corresponding wait state we are not giving back a valid word
    // -> throw an error
    if (capture_dr && state_q inside {Read, WaitReadValid}) begin
      error_dmi_busy = 1'b1;
    end

    if (error_dmi_busy) begin
      error_d = DMIBusy;
    end
    // clear sticky error flag
    if (update_dr && dmi_reset && dtmcs_select) begin
      error_d = DMINoError;
    end
  end

  // shift register
  assign dmi_tdo = dr_q[0];

  always_comb begin : p_shift
    dr_d    = dr_q;

    if (capture_dr) begin
      if (dmi_access) begin
        if (error_q == DMINoError && !error_dmi_busy) begin
          dr_d = {address_q, data_q, DMINoError};
        // DMI was busy, report an error
        end else if (error_q == DMIBusy || error_dmi_busy) begin
          dr_d = {address_q, data_q, DMIBusy};
        end
      end
    end

    if (shift_dr) begin
      if (dmi_access) begin
        dr_d = {dmi_tdi, dr_q[$bits(dr_q)-1:1]};
      end
    end

    if (test_logic_reset) begin
      dr_d = '0;
    end
  end

  always_ff @(posedge tck_i or negedge trst_ni) begin : p_regs
    if (!trst_ni) begin
      dr_q      <= '0;
      state_q   <= Idle;
      address_q <= '0;
      data_q    <= '0;
      error_q   <= DMINoError;
    end else begin
      dr_q      <= dr_d;
      state_q   <= state_d;
      address_q <= address_d;
      data_q    <= data_d;
      error_q   <= error_d;
    end
  end

  // ---------
  // TAP
  // ---------
  dmi_jtag_tap #(
    .IrLength (5),
    .IdcodeValue(IdcodeValue)
  ) i_dmi_jtag_tap (
    .tck_i,
    .tms_i,
    .trst_ni,
    .td_i,
    .td_o,
    .tdo_oe_o,
    .testmode_i,
    .test_logic_reset_o ( test_logic_reset ),
    .shift_dr_o         ( shift_dr         ),
    .update_dr_o        ( update_dr        ),
    .capture_dr_o       ( capture_dr       ),
    .dmi_access_o       ( dmi_access       ),
    .dtmcs_select_o     ( dtmcs_select     ),
    .dmi_reset_o        ( dmi_reset        ),
    .dmi_error_i        ( error_q          ),
    .dmi_tdi_o          ( dmi_tdi          ),
    .dmi_tdo_i          ( dmi_tdo          )
  );

  // ---------
  // CDC
  // ---------
  dmi_cdc i_dmi_cdc (
    // JTAG side (master side)
    .tck_i,
    .trst_ni,
    .jtag_dmi_req_i    ( dmi_req          ),
    .jtag_dmi_ready_o  ( dmi_req_ready    ),
    .jtag_dmi_valid_i  ( dmi_req_valid    ),
    .jtag_dmi_resp_o   ( dmi_resp         ),
    .jtag_dmi_valid_o  ( dmi_resp_valid   ),
    .jtag_dmi_ready_i  ( dmi_resp_ready   ),
    // core side
    .clk_i,
    .rst_ni,
    .core_dmi_req_o    ( dmi_req_o        ),
    .core_dmi_valid_o  ( dmi_req_valid_o  ),
    .core_dmi_ready_i  ( dmi_req_ready_i  ),
    .core_dmi_resp_i   ( dmi_resp_i       ),
    .core_dmi_ready_o  ( dmi_resp_ready_o ),
    .core_dmi_valid_i  ( dmi_resp_valid_i )
  );

endmodule : dmi_jtag
