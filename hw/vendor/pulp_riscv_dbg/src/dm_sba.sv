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
* File:   dm_sba.sv
* Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
* Date:   1.8.2018
*
* Description: System Bus Access Module
*
*/
module dm_sba #(
  parameter int unsigned BusWidth = 32,
  parameter bit          ReadByteEnable = 1
) (
  input  logic                   clk_i,       // Clock
  input  logic                   rst_ni,
  input  logic                   dmactive_i,  // synchronous reset active low

  output logic                   master_req_o,
  output logic [BusWidth-1:0]    master_add_o,
  output logic                   master_we_o,
  output logic [BusWidth-1:0]    master_wdata_o,
  output logic [BusWidth/8-1:0]  master_be_o,
  input  logic                   master_gnt_i,
  input  logic                   master_r_valid_i,
  input  logic                   master_r_err_i,
  input  logic                   master_r_other_err_i, // *other_err_i has priority over *err_i
  input  logic [BusWidth-1:0]    master_r_rdata_i,

  input  logic [BusWidth-1:0]    sbaddress_i,
  input  logic                   sbaddress_write_valid_i,
  // control signals in
  input  logic                   sbreadonaddr_i,
  output logic [BusWidth-1:0]    sbaddress_o,
  input  logic                   sbautoincrement_i,
  input  logic [2:0]             sbaccess_i,
  // data in
  input  logic                   sbreadondata_i,
  input  logic [BusWidth-1:0]    sbdata_i,
  input  logic                   sbdata_read_valid_i,
  input  logic                   sbdata_write_valid_i,
  // read data out
  output logic [BusWidth-1:0]    sbdata_o,
  output logic                   sbdata_valid_o,
  // control signals
  output logic                   sbbusy_o,
  output logic                   sberror_valid_o, // bus error occurred
  output logic [2:0]             sberror_o // bus error occurred
);

  localparam int BeIdxWidth = $clog2(BusWidth/8);
  dm::sba_state_e state_d, state_q;

  logic [BusWidth-1:0]           address;
  logic                          req;
  logic                          gnt;
  logic                          we;
  logic [BusWidth/8-1:0]         be;
  logic [BusWidth/8-1:0]         be_mask;
  logic [BeIdxWidth-1:0] be_idx;

  assign sbbusy_o = logic'(state_q != dm::Idle);

  always_comb begin : p_be_mask
    be_mask = '0;

    // generate byte enable mask
    unique case (sbaccess_i)
      3'b000: begin
        be_mask[be_idx] = '1;
      end
      3'b001: begin
        be_mask[int'({be_idx[$high(be_idx):1], 1'b0}) +: 2] = '1;
      end
      3'b010: begin
        if (BusWidth == 32'd64) be_mask[int'({be_idx[$high(be_idx)], 2'h0}) +: 4] = '1;
        else                    be_mask = '1;
      end
      3'b011: be_mask = '1;
      default: ;
    endcase
  end

  logic [BusWidth-1:0] sbaccess_mask;
  assign sbaccess_mask = {BusWidth{1'b1}} << sbaccess_i;

  logic addr_incr_en;
  logic [BusWidth-1:0] addr_incr;
  assign addr_incr = (addr_incr_en) ? (BusWidth'(1'b1) << sbaccess_i) : '0;
  assign sbaddress_o = sbaddress_i + addr_incr;


  always_comb begin : p_fsm
    req     = 1'b0;
    address = sbaddress_i;
    we      = 1'b0;
    be      = '0;
    be_idx  = sbaddress_i[BeIdxWidth-1:0];

    sberror_o       = '0;
    sberror_valid_o = 1'b0;

    addr_incr_en    = 1'b0;

    state_d = state_q;

    unique case (state_q)
      dm::Idle: begin
        // debugger requested a read
        if (sbaddress_write_valid_i && sbreadonaddr_i)  state_d = dm::Read;
        // debugger requested a write
        if (sbdata_write_valid_i) state_d = dm::Write;
        // perform another read
        if (sbdata_read_valid_i && sbreadondata_i) state_d = dm::Read;
      end

      dm::Read: begin
        req = 1'b1;
        if (ReadByteEnable) be = be_mask;
        if (gnt) state_d = dm::WaitRead;
      end

      dm::Write: begin
        req = 1'b1;
        we  = 1'b1;
        be = be_mask;
        if (gnt) state_d = dm::WaitWrite;
      end

      dm::WaitRead: begin
        if (sbdata_valid_o) begin
          state_d = dm::Idle;
          // auto-increment address
          addr_incr_en = sbautoincrement_i;
          // check whether an "other" error has been encountered.
          if (master_r_other_err_i) begin
            sberror_valid_o = 1'b1;
            sberror_o = 3'd7;
          // check whether there was a bus error (== bad address).
          end else if (master_r_err_i) begin
            sberror_valid_o = 1'b1;
            sberror_o = 3'd2;
          end
        end
      end

      dm::WaitWrite: begin
        if (sbdata_valid_o) begin
          state_d = dm::Idle;
          // auto-increment address
          addr_incr_en = sbautoincrement_i;
          // check whether an "other" error has been encountered.
          if (master_r_other_err_i) begin
            sberror_valid_o = 1'b1;
            sberror_o = 3'd7;
          // check whether there was a bus error (== bad address).
          end else if (master_r_err_i) begin
            sberror_valid_o = 1'b1;
            sberror_o = 3'd2;
          end
        end
      end

      default: state_d = dm::Idle; // catch parasitic state
    endcase

    // handle error case
    if (32'(sbaccess_i) > BeIdxWidth && state_q != dm::Idle) begin
      req             = 1'b0;
      state_d         = dm::Idle;
      sberror_valid_o = 1'b1;
      sberror_o       = 3'd4; // unsupported size was requested
    end

    //if sbaccess_i lsbs of address are not 0 - report misalignment error
    if (|(sbaddress_i & ~sbaccess_mask) && state_q != dm::Idle) begin
      req             = 1'b0;
      state_d         = dm::Idle;
      sberror_valid_o = 1'b1;
      sberror_o       = 3'd3; // alignment error
    end
    // further error handling should go here ...
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= dm::Idle;
    end else begin
      state_q <= state_d;
    end
  end

  logic [BeIdxWidth-1:0] be_idx_masked;
  assign be_idx_masked   = be_idx & BeIdxWidth'(sbaccess_mask);
  assign master_req_o    = req;
  assign master_add_o    = address[BusWidth-1:0];
  assign master_we_o     = we;
  assign master_wdata_o  = sbdata_i[BusWidth-1:0] << (8 * be_idx_masked);
  assign master_be_o     = be[BusWidth/8-1:0];
  assign gnt             = master_gnt_i;
  assign sbdata_valid_o  = master_r_valid_i;
  assign sbdata_o        = master_r_rdata_i[BusWidth-1:0] >> (8 * be_idx_masked);

endmodule : dm_sba
