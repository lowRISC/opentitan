// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Load Store Unit
 *
 * Load Store Unit, used to eliminate multiple access during processor stalls,
 * and to align bytes and halfwords.
 */
module ibex_load_store_unit (
    input  logic         clk_i,
    input  logic         rst_ni,

    // data interface
    output logic         data_req_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i,
    input  logic         data_err_i,
    input  logic         data_pmp_err_i,

    output logic [31:0]  data_addr_o,
    output logic         data_we_o,
    output logic [3:0]   data_be_o,
    output logic [31:0]  data_wdata_o,
    input  logic [31:0]  data_rdata_i,

    // signals to/from ID/EX stage
    input  logic         data_we_ex_i,         // write enable                     -> from ID/EX
    input  logic [1:0]   data_type_ex_i,       // data type: word, half word, byte -> from ID/EX
    input  logic [31:0]  data_wdata_ex_i,      // data to write to memory          -> from ID/EX
    input  logic         data_sign_ext_ex_i,   // sign extension                   -> from ID/EX

    output logic [31:0]  data_rdata_ex_o,      // requested data                   -> to ID/EX
    input  logic         data_req_ex_i,        // data request                     -> from ID/EX

    input  logic [31:0]  adder_result_ex_i,    // address computed in ALU          -> from ID/EX

    output logic         addr_incr_req_o,      // request address increment for
                                               // misaligned accesses              -> to ID/EX
    output logic [31:0]  addr_last_o,          // address of last transaction      -> to controller
                                               // -> mtval
                                               // -> AGU for misaligned accesses
    output logic         data_valid_o,         // LSU has completed transaction    -> to

    // exception signals
    output logic         load_err_o,
    output logic         store_err_o,

    output logic         busy_o
);

  logic [31:0]  data_addr;
  logic [31:0]  data_addr_w_aligned;
  logic [31:0]  addr_last_q, addr_last_d;

  logic         data_update;
  logic [31:0]  rdata_q, rdata_d;
  logic [1:0]   rdata_offset_q, rdata_offset_d;
  logic [1:0]   data_type_q, data_type_d;
  logic         data_sign_ext_q, data_sign_ext_d;
  logic         data_we_q, data_we_d;

  logic [1:0]   wdata_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [31:0]  data_wdata;

  logic [31:0]  data_rdata_ext;

  logic [31:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         split_misaligned_access;
  logic         handle_misaligned_q, handle_misaligned_d; // high after receiving grant for first
                                                          // part of a misaligned access
  logic         pmp_err_d;
  logic         pmp_err_q;
  logic         data_or_pmp_err;

  typedef enum logic [2:0]  {
    IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT, WAIT_RVALID,
    WAIT_GNT_ERR, WAIT_RVALID_ERR, WAIT_RVALID_DONE
  } ls_fsm_e;

  ls_fsm_e ls_fsm_cs, ls_fsm_ns;

  assign data_addr = adder_result_ex_i;

  ///////////////////
  // BE generation //
  ///////////////////

  always_comb begin
    unique case (data_type_ex_i) // Data type 00 Word, 01 Half word, 11,10 byte
      2'b00: begin // Writing a word
        if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
          unique case (data_addr[1:0])
            2'b00:   data_be = 4'b1111;
            2'b01:   data_be = 4'b1110;
            2'b10:   data_be = 4'b1100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 'X;
          endcase // case (data_addr[1:0])
        end else begin // second part of misaligned transaction
          unique case (data_addr[1:0])
            2'b00:   data_be = 4'b0000; // this is not used, but included for completeness
            2'b01:   data_be = 4'b0001;
            2'b10:   data_be = 4'b0011;
            2'b11:   data_be = 4'b0111;
            default: data_be = 'X;
          endcase // case (data_addr[1:0])
        end
      end

      2'b01: begin // Writing a half word
        if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
          unique case (data_addr[1:0])
            2'b00:   data_be = 4'b0011;
            2'b01:   data_be = 4'b0110;
            2'b10:   data_be = 4'b1100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 'X;
          endcase // case (data_addr[1:0])
        end else begin // second part of misaligned transaction
          data_be = 4'b0001;
        end
      end

      2'b10,
      2'b11: begin // Writing a byte
        unique case (data_addr[1:0])
          2'b00:   data_be = 4'b0001;
          2'b01:   data_be = 4'b0010;
          2'b10:   data_be = 4'b0100;
          2'b11:   data_be = 4'b1000;
          default: data_be = 'X;
        endcase // case (data_addr[1:0])
      end

      default:     data_be = 'X;
    endcase // case (data_type_ex_i)
  end

  /////////////////////
  // WData alignment //
  /////////////////////

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses here
  assign wdata_offset = data_addr[1:0];
  always_comb begin
    unique case (wdata_offset)
      2'b00:   data_wdata =  data_wdata_ex_i[31:0];
      2'b01:   data_wdata = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};
      2'b10:   data_wdata = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};
      2'b11:   data_wdata = {data_wdata_ex_i[ 7:0], data_wdata_ex_i[31: 8]};
      default: data_wdata = 'X;
    endcase // case (wdata_offset)
  end

  /////////////////////
  // RData alignment //
  /////////////////////

  // rdata_q holds data returned from memory for first part of misaligned loads
  always_comb begin
    rdata_d = rdata_q;
    if (data_rvalid_i & ~data_we_q & handle_misaligned_q) begin
      rdata_d = data_rdata_i;
    end
  end

  // update control signals for next read data upon receiving grant
  // This must also be set for a pmp error (which might not actually be granted) to force
  // data_we_q to update in order to signal the correct exception type (load or store)
  // Note that we can use the registered pmp_err_q here since we will always take an
  // extra cycle to progress to the RVALID state
  assign data_update = data_gnt_i | pmp_err_q;

  assign rdata_offset_d  = data_update ? data_addr[1:0]     : rdata_offset_q;
  assign data_type_d     = data_update ? data_type_ex_i     : data_type_q;
  assign data_sign_ext_d = data_update ? data_sign_ext_ex_i : data_sign_ext_q;
  assign data_we_d       = data_update ? data_we_ex_i       : data_we_q;

  // registers for rdata alignment and sign-extension
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_q         <=   '0;
      rdata_offset_q  <= 2'h0;
      data_type_q     <= 2'h0;
      data_sign_ext_q <= 1'b0;
      data_we_q       <= 1'b0;
    end else begin
      rdata_q         <= rdata_d;
      rdata_offset_q  <= rdata_offset_d;
      data_type_q     <= data_type_d;
      data_sign_ext_q <= data_sign_ext_d;
      data_we_q       <= data_we_d;
    end
  end

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext =  data_rdata_i[31:0];
      2'b01:   rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext = 'X;
    endcase
  end

  ////////////////////
  // Sign extension //
  ////////////////////

  // sign extension for half words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
        end
      end

      default: rdata_h_ext = 'X;
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
        end
      end

      default: rdata_b_ext = 'X;
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    unique case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
      default:     data_rdata_ext = 'X;
    endcase //~case(rdata_type_q)
  end

  /////////////
  // LSU FSM //
  /////////////

  // check for misaligned accesses that need to be split into two word-aligned accesses
  assign split_misaligned_access =
      ((data_type_ex_i == 2'b00) && (data_addr[1:0] != 2'b00)) || // misaligned word access
      ((data_type_ex_i == 2'b01) && (data_addr[1:0] == 2'b11));   // misaligned half-word access

  // FSM
  always_comb begin
    ls_fsm_ns       = ls_fsm_cs;

    data_req_o          = 1'b0;
    data_valid_o        = 1'b0;
    addr_incr_req_o     = 1'b0;
    handle_misaligned_d = handle_misaligned_q;
    data_or_pmp_err     = 1'b0;
    pmp_err_d           = pmp_err_q;

    unique case (ls_fsm_cs)

      IDLE: begin
        if (data_req_ex_i) begin
          data_req_o = 1'b1;
          pmp_err_d  = data_pmp_err_i;
          if (data_gnt_i) begin
            handle_misaligned_d = split_misaligned_access;
            ls_fsm_ns           = split_misaligned_access ? WAIT_RVALID_MIS : WAIT_RVALID;
          end else begin
            ls_fsm_ns           = split_misaligned_access ? WAIT_GNT_MIS    : WAIT_GNT;
          end
        end
      end

      WAIT_GNT_MIS: begin
        data_req_o = 1'b1;
        // data_pmp_err_i is valid during the address phase of a request. An error will block the
        // external request and so a data_gnt_i might never be signalled. The registered version
        // pmp_err_q is only updated for new address phases and so can be used in WAIT_GNT* and
        // WAIT_RVALID* states
        if (data_gnt_i || pmp_err_q) begin
          handle_misaligned_d = 1'b1;
          ls_fsm_ns           = WAIT_RVALID_MIS;
        end
      end

      WAIT_RVALID_MIS: begin
        // push out second request
        data_req_o = 1'b1;
        // tell ID/EX stage to update the address
        addr_incr_req_o = 1'b1;

        // first part rvalid is received, or gets a PMP error
        if (data_rvalid_i || pmp_err_q) begin
          // Update the PMP error for the second part
          pmp_err_d = data_pmp_err_i;
          if (pmp_err_q || data_err_i) begin
            // first part created an error, abort transaction
            data_valid_o        = 1'b1;
            data_or_pmp_err     = 1'b1;
            handle_misaligned_d = 1'b0;
            // If already granted, wait for second rvalid
            ls_fsm_ns = data_gnt_i ? WAIT_RVALID_ERR : WAIT_GNT_ERR;

          end else begin
            // No error in first part, proceed with second part
            ls_fsm_ns = data_gnt_i ? WAIT_RVALID : WAIT_GNT;
          end

        end else begin
          // first part rvalid is NOT received
          if (data_gnt_i) begin
            // second grant is received
            ls_fsm_ns = WAIT_RVALID_DONE;
          end
        end
      end

      WAIT_GNT: begin
        // tell ID/EX stage to update the address
        addr_incr_req_o = handle_misaligned_q;
        data_req_o      = 1'b1;
        if (data_gnt_i || pmp_err_q) begin
          ls_fsm_ns = WAIT_RVALID;
        end
      end

      WAIT_RVALID: begin
        data_req_o = 1'b0;
        if (data_rvalid_i || pmp_err_q) begin
          data_valid_o        = 1'b1;
          data_or_pmp_err     = data_err_i | pmp_err_q;
          handle_misaligned_d = 1'b0;
          ls_fsm_ns           = IDLE;
        end else begin
          ls_fsm_ns           = WAIT_RVALID;
        end
      end

      WAIT_GNT_ERR: begin
        // Wait for the grant of the abandoned second access
        data_req_o = 1'b1;
        // tell ID/EX stage to update the address
        addr_incr_req_o = 1'b1;
        if (pmp_err_q) begin
          // The second part was suppressed by a PMP error
          ls_fsm_ns = IDLE;
        end else if (data_gnt_i) begin
          ls_fsm_ns = WAIT_RVALID_ERR;
        end
      end

      WAIT_RVALID_ERR: begin
        // Wait for the rvalid, but do nothing with it
        if (data_rvalid_i || pmp_err_q) begin
          ls_fsm_ns = IDLE;
        end
      end

      WAIT_RVALID_DONE: begin
        // Wait for the first rvalid, second request is already granted
        if (data_rvalid_i) begin
          // Update the pmp error for the second part
          pmp_err_d = data_pmp_err_i;
          // The first part cannot see a PMP error in this state
          if (data_err_i) begin
            // first part created an error, abort transaction and wait for second rvalid
            data_valid_o        = 1'b1;
            data_or_pmp_err     = 1'b1;
            handle_misaligned_d = 1'b0;
            ls_fsm_ns           = WAIT_RVALID_ERR;
          end else begin
            ls_fsm_ns           = WAIT_RVALID;
          end
        end
      end

      default: begin
        ls_fsm_ns = ls_fsm_e'(1'bX);
      end
    endcase
  end

  // store last address for mtval + AGU for misaligned transactions:
  // - misaligned address needed for correct generation of data_be and data_rdata_ext
  // - do not update in case of errors, mtval needs the failing address
  always_comb begin
    addr_last_d = addr_last_q;
    if (data_req_o & data_gnt_i & ~(load_err_o | store_err_o)) begin
      addr_last_d = data_addr;
    end
  end

  // registers for FSM
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ls_fsm_cs           <= IDLE;
      addr_last_q         <= '0;
      handle_misaligned_q <= '0;
      pmp_err_q           <= '0;
    end else begin
      ls_fsm_cs           <= ls_fsm_ns;
      addr_last_q         <= addr_last_d;
      handle_misaligned_q <= handle_misaligned_d;
      pmp_err_q           <= pmp_err_d;
    end
  end

  /////////////
  // Outputs //
  /////////////

  // output to register file
  assign data_rdata_ex_o = data_rdata_ext;

  // output data address must be word aligned
  assign data_addr_w_aligned = {data_addr[31:2], 2'b00};

  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;
  assign data_wdata_o  = data_wdata;
  assign data_we_o     = data_we_ex_i;
  assign data_be_o     = data_be;

  // output to ID stage: mtval + AGU for misaligned transactions
  assign addr_last_o   = addr_last_q;

  // Signal a load or store error depending on the transaction type outstanding
  assign load_err_o    = data_or_pmp_err & ~data_we_q;
  assign store_err_o   = data_or_pmp_err &  data_we_q;

  assign busy_o = (ls_fsm_cs != IDLE);

  ////////////////
  // Assertions //
  ////////////////

`ifndef VERILATOR
  // make sure there is no new request when the old one is not yet completely done
  // i.e. it should not be possible to get a grant without an rvalid for the
  // last request
  assert property (
    @(posedge clk_i)
      ((ls_fsm_cs == WAIT_RVALID) && (data_gnt_i == 1'b1)) |-> (data_rvalid_i == 1'b1) ) else
        $display("Data grant set while LSU keeps waiting for rvalid");

  // there should be no rvalid when we are in IDLE
  assert property (
    @(posedge clk_i) (ls_fsm_cs == IDLE) |-> (data_rvalid_i == 1'b0) ) else
      $display("Data rvalid set while LSU idle");

  // assert that errors are only sent at the same time as rvalid
  assert property (
    @(posedge clk_i) (data_err_i) |-> (data_rvalid_i) ) else
      $display("Data error not sent with rvalid");

  // assert that the address does not contain X when request is sent
  assert property (
    @(posedge clk_i) (data_req_o) |-> (!$isunknown(data_addr_o)) ) else
      $display("Data address not valid");

  // assert that the address is word aligned when request is sent
  assert property (
    @(posedge clk_i) (data_req_o) |-> (data_addr_o[1:0] == 2'b00) ) else
      $display("Data address not word aligned");
`endif
endmodule
