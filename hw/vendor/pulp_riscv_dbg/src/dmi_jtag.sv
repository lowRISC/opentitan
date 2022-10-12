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
  input  logic         test_rst_ni,

  // active-low glitch free reset signal. Is asserted
  // (clk_i) whenever the dmi_jtag is reset.
  output logic         dmi_rst_no,
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

  typedef enum logic [1:0] {
    DMINoError = 2'h0, DMIReservedError = 2'h1,
    DMIOPFailed = 2'h2, DMIBusy = 2'h3
  } dmi_error_e;
  dmi_error_e error_d, error_q;

  logic tck;
  logic jtag_dmi_clear; // Synchronous reset of DMI triggered by TestLogicReset in
                        // jtag TAP
  logic dmi_clear; // Functional (warm) reset of the entire DMI
  logic update;
  logic capture;
  logic shift;
  logic tdi;

  logic dtmcs_select;
  dm::dtmcs_t dtmcs_d, dtmcs_q;

  assign dmi_clear = jtag_dmi_clear || (dtmcs_select && update && dtmcs_q.dmihardreset);

  // -------------------------------
  // Debug Module Control and Status
  // -------------------------------

  always_comb begin
    dtmcs_d = dtmcs_q;
    if (capture) begin
      if (dtmcs_select) begin
        dtmcs_d  = '{
                      zero1        : '0,
                      dmihardreset : 1'b0,
                      dmireset     : 1'b0,
                      zero0        : '0,
                      idle         : 3'd1, // 1: Enter Run-Test/Idle and leave it immediately
                      dmistat      : error_q, // 0: No error, 2: Op failed, 3: too fast
                      abits        : 6'd7, // The size of address in dmi
                      version      : 4'd1  // Version described in spec version 0.13 (and later?)
                    };
      end
    end

    if (shift) begin
      if (dtmcs_select) dtmcs_d  = {tdi, 31'(dtmcs_q >> 1)};
    end
  end

  always_ff @(posedge tck or negedge trst_ni) begin
    if (!trst_ni) begin
      dtmcs_q <= '0;
    end else begin
      dtmcs_q <= dtmcs_d;
    end
  end

  // ----------------------------
  // DMI (Debug Module Interface)
  // ----------------------------

  logic        dmi_select;
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
  // We will always be ready to accept the data we requested.
  assign dmi_resp_ready = 1'b1;

  logic error_dmi_busy;
  logic error_dmi_op_failed;

  always_comb begin : p_fsm
    error_dmi_busy = 1'b0;
    error_dmi_op_failed = 1'b0;
    // default assignments
    state_d   = state_q;
    address_d = address_q;
    data_d    = data_q;
    error_d   = error_q;

    dmi_req_valid = 1'b0;

    if (dmi_clear) begin
      state_d   = Idle;
      data_d    = '0;
      error_d   = DMINoError;
      address_d = '0;
    end else begin
      unique case (state_q)
        Idle: begin
          // make sure that no error is sticky
          if (dmi_select && update && (error_q == DMINoError)) begin
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
            unique case (dmi_resp.resp)
              dm::DTM_SUCCESS: begin
                data_d = dmi_resp.data;
              end
              dm::DTM_ERR: begin
                data_d = 32'hDEAD_BEEF;
                error_dmi_op_failed = 1'b1;
              end
              dm::DTM_BUSY: begin
                data_d = 32'hB051_B051;
                error_dmi_busy = 1'b1;
              end
              default: begin
                data_d = 32'hBAAD_C0DE;
              end
            endcase
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
            unique case (dmi_resp.resp)
              dm::DTM_ERR: error_dmi_op_failed = 1'b1;
              dm::DTM_BUSY: error_dmi_busy = 1'b1;
              default: ;
            endcase
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

      // update means we got another request but we didn't finish
      // the one in progress, this state is sticky
      if (update && state_q != Idle) begin
        error_dmi_busy = 1'b1;
      end

      // if capture goes high while we are in the read state
      // or in the corresponding wait state we are not giving back a valid word
      // -> throw an error
      if (capture && state_q inside {Read, WaitReadValid}) begin
        error_dmi_busy = 1'b1;
      end

      if (error_dmi_busy && error_q == DMINoError) begin
        error_d = DMIBusy;
      end

      if (error_dmi_op_failed && error_q == DMINoError) begin
        error_d = DMIOPFailed;
      end

      // clear sticky error flag
      if (update && dtmcs_q.dmireset && dtmcs_select) begin
        error_d = DMINoError;
      end
    end
  end

  // shift register
  assign dmi_tdo = dr_q[0];

  always_comb begin : p_shift
    dr_d    = dr_q;
    if (dmi_clear) begin
      dr_d = '0;
    end else begin
      if (capture) begin
        if (dmi_select) begin
          if (error_q == DMINoError && !error_dmi_busy) begin
            dr_d = {address_q, data_q, DMINoError};
            // DMI was busy, report an error
          end else if (error_q == DMIBusy || error_dmi_busy) begin
            dr_d = {address_q, data_q, DMIBusy};
          end
        end
      end

      if (shift) begin
        if (dmi_select) begin
          dr_d = {tdi, dr_q[$bits(dr_q)-1:1]};
        end
      end
    end
  end

  always_ff @(posedge tck or negedge trst_ni) begin
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
    .tck_o          ( tck              ),
    .dmi_clear_o    ( jtag_dmi_clear   ),
    .update_o       ( update           ),
    .capture_o      ( capture          ),
    .shift_o        ( shift            ),
    .tdi_o          ( tdi              ),
    .dtmcs_select_o ( dtmcs_select     ),
    .dtmcs_tdo_i    ( dtmcs_q[0]       ),
    .dmi_select_o   ( dmi_select       ),
    .dmi_tdo_i      ( dmi_tdo          )
  );

  // ---------
  // CDC
  // ---------
  dmi_cdc i_dmi_cdc (
    // Test controls
    .testmode_i,
    .test_rst_ni,
    // JTAG side (master side)
    .tck_i                ( tck              ),
    .trst_ni              ( trst_ni          ),
    .jtag_dmi_cdc_clear_i ( dmi_clear        ),
    .jtag_dmi_req_i       ( dmi_req          ),
    .jtag_dmi_ready_o     ( dmi_req_ready    ),
    .jtag_dmi_valid_i     ( dmi_req_valid    ),
    .jtag_dmi_resp_o      ( dmi_resp         ),
    .jtag_dmi_valid_o     ( dmi_resp_valid   ),
    .jtag_dmi_ready_i     ( dmi_resp_ready   ),
    // core side
    .clk_i,
    .rst_ni,
    .core_dmi_rst_no      ( dmi_rst_no       ),
    .core_dmi_req_o       ( dmi_req_o        ),
    .core_dmi_valid_o     ( dmi_req_valid_o  ),
    .core_dmi_ready_i     ( dmi_req_ready_i  ),
    .core_dmi_resp_i      ( dmi_resp_i       ),
    .core_dmi_ready_o     ( dmi_resp_ready_o ),
    .core_dmi_valid_i     ( dmi_resp_valid_i )
  );

endmodule : dmi_jtag
