// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Load Store Unit
 *
 * Load Store Unit, used to eliminate multiple access during processor stalls,
 * and to align bytes and halfwords.
 */

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

module ibex_load_store_unit import ibex_pkg::*; import ibex_cheriot_pkg::*; #(
  parameter base_isa_e   BaseIsa      = BaseIsaRV32I,
  parameter bit          MemECC       = 1'b0,
  parameter int unsigned MemDataWidth = MemECC ? 32 + 7 : 32
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  ibex_mubi_t   cheriot_enable_i,

  // data interface
  output logic         data_req_o,
  input  logic         data_gnt_i,
  input  logic         data_rvalid_i,
  input  logic         data_bus_err_i,
  input  logic         data_pmp_err_i,

  output logic [31:0]             data_addr_o,
  output logic                    data_we_o,
  output logic [3:0]              data_be_o,
  output logic [MemDataWidth-1:0] data_wdata_o,
  output logic                    data_tag_o,
  input  logic [MemDataWidth-1:0] data_rdata_i,
  input  logic                    data_tag_i,

  // signals to/from ID/EX stage
  input  logic         lsu_we_i,             // write enable                     -> from ID/EX
  input  logic         lsu_is_cap_i,         // capability load/store            -> from ID/EX
  input  logic         lsu_cheriot_err_i,    // CHERIoT access error               -> from ID/EX
  input  logic [1:0]   lsu_type_i,           // data type: word, half word, byte -> from ID/EX
  input  logic [31:0]  lsu_wdata_i,          // data to write to memory          -> from ID/EX
  input  cap_t         lsu_wcap_i,           // capability to write to memory    -> from ID/EX
  input  cap_clrperm_t lsu_lc_clrperm_i,     // cap load clear permissions       -> from ID/EX
  input  logic         lsu_sign_ext_i,       // sign extension                   -> from ID/EX

  output cap_t         lsu_rcap_o,           // capability read from memory      -> to ID/EX
  output logic [31:0]  lsu_rdata_o,          // requested data                   -> to ID/EX
  output logic         lsu_rdata_valid_o,
  input  logic         lsu_req_i,            // data request                     -> from ID/EX

  input  logic [31:0]  adder_result_ex_i,    // address computed in ALU          -> from ID/EX

  output logic         addr_incr_req_o,      // request address increment for
                                             // misaligned accesses              -> to ID/EX
  output logic [31:0]  addr_last_o,          // address of last transaction      -> to controller
                                             // -> mtval
                                             // -> AGU for misaligned accesses

  output logic         lsu_req_done_o,       // Signals that data request is complete
                                             // (only need to await final data
                                             // response)                        -> to ID/EX

  output logic         lsu_resp_valid_o,     // LSU has response from transaction -> to ID/EX & WB

  // exception signals
  output logic         load_err_o,
  output logic         load_resp_intg_err_o,
  output logic         store_err_o,
  output logic         store_resp_intg_err_o,
  output logic         lsu_err_is_cheriot_o,

  output logic         busy_o,

  output logic         perf_load_o,
  output logic         perf_store_o
);

  logic [31:0]  data_addr;
  logic [31:0]  data_addr_w_aligned;
  logic [31:0]  addr_last_q, addr_last_d;

  logic         addr_update;
  logic         ctrl_update;
  logic         rdata_update;
  logic [31:8]  rdata_q;
  logic [1:0]   rdata_offset_q;
  logic [1:0]   data_type_q;
  logic         data_sign_ext_q;
  logic         data_we_q;

  logic [1:0]   data_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [31:0]  data_wdata_data;
  logic         data_wdata_tag;

  logic [31:0]  data_rdata_ext;

  logic [31:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         split_misaligned_access;
  logic         handle_misaligned_q, handle_misaligned_d; // high after receiving grant for first
                                                          // part of a misaligned access
  logic         pmp_err_q, pmp_err_d;
  logic         lsu_err_q, lsu_err_d;
  logic         data_intg_err, data_or_pmp_err;

  logic         resp_is_cap_q;
  logic         cheriot_err_d, cheriot_err_q;
  cap_clrperm_t resp_lc_clrperm_q;
  logic         lsu_go, lsu_go_goodcap;
  logic         cpu_req_erred, cpu_req_valid;

  ls_fsm_e      ls_fsm_cs, ls_fsm_ns;

  cap_rx_fsm_t  cap_rx_fsm_q, cap_rx_fsm_d;

  logic         cap_lsw_err_q;
  logic [31:0]  cap_lsw_data_q;
  logic         cap_lsw_tag_q;

  assign data_addr   = adder_result_ex_i;
  assign data_offset = ((BaseIsa == BaseIsaRV32IorCHERIoT) &
                        (cheriot_enable_i == IbexMuBiOn) & lsu_is_cap_i) ? 2'b00 : data_addr[1:0];

  ///////////////////
  // BE generation //
  ///////////////////

  always_comb begin
    if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) & lsu_is_cap_i)
      data_be = 4'b1111;                  // caps are always word aligned
    else begin
      unique case (lsu_type_i) // Data type 00 Word, 01 Half word, 11,10 byte
        2'b00: begin // Writing a word
          if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b1111;
              2'b01:   data_be = 4'b1110;
              2'b10:   data_be = 4'b1100;
              2'b11:   data_be = 4'b1000;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end else begin // second part of misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b0000; // this is not used, but included for completeness
              2'b01:   data_be = 4'b0001;
              2'b10:   data_be = 4'b0011;
              2'b11:   data_be = 4'b0111;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end
        end

        2'b01: begin // Writing a half word
          if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b0011;
              2'b01:   data_be = 4'b0110;
              2'b10:   data_be = 4'b1100;
              2'b11:   data_be = 4'b1000;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end else begin // second part of misaligned transaction
            data_be = 4'b0001;
          end
        end

        2'b10,
        2'b11: begin // Writing a byte
          unique case (data_offset)
            2'b00:   data_be = 4'b0001;
            2'b01:   data_be = 4'b0010;
            2'b10:   data_be = 4'b0100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 4'b1111;
          endcase // case (data_offset)
        end

        default:     data_be = 4'b1111;
      endcase // case (lsu_type_i)
    end  // if lsu_cap
  end

  /////////////////////
  // WData alignment //
  /////////////////////

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses here
  logic [31:0] wdata_int;
  always_comb begin
    unique case (data_offset)
      2'b00:   wdata_int = lsu_wdata_i;
      2'b01:   wdata_int = {lsu_wdata_i[23:0], lsu_wdata_i[31:24]};
      2'b10:   wdata_int = {lsu_wdata_i[15:0], lsu_wdata_i[31:16]};
      2'b11:   wdata_int = {lsu_wdata_i[ 7:0], lsu_wdata_i[31: 8]};
      default: wdata_int = lsu_wdata_i;
    endcase // case (data_offset)
  end

  always_comb begin
    if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) & lsu_is_cap_i) begin
      if (lsu_we_i & (ls_fsm_cs == CTX_WAIT_GNT2))
        {data_wdata_tag, data_wdata_data} = cheriot_cap_to_mem(lsu_wcap_i);
      else if (lsu_we_i)
        {data_wdata_tag, data_wdata_data} = {lsu_wcap_i.valid, lsu_wdata_i};
      else
        // cap load: tag=1 signals capability read to memory
        {data_wdata_tag, data_wdata_data} = {1'b1, lsu_wdata_i};
    end else
      {data_wdata_tag, data_wdata_data} = {1'b0, wdata_int};
  end
  // correction-factor bits are consumed by cheriot_cap_to_mem but the linter's
  // hierarchical analysis doesn't trace through function bodies
  logic [1:0] unused_lsu_wcap_cor;
  assign unused_lsu_wcap_cor = lsu_wcap_i.cap_cor;
  /////////////////////
  // RData alignment //
  /////////////////////

  // register for unaligned rdata
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_q <= '0;
    end else if (rdata_update) begin
      rdata_q <= data_rdata_i[31:8];
    end
  end

  // registers for transaction control
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_offset_q  <= 2'h0;
      data_type_q     <= 2'h0;
      data_sign_ext_q <= 1'b0;
      data_we_q       <= 1'b0;
    end else if (ctrl_update) begin
      rdata_offset_q  <= data_offset;
      data_type_q     <= lsu_type_i;
      data_sign_ext_q <= lsu_sign_ext_i;
      data_we_q       <= lsu_we_i;
    end
  end

  // Store last address for mtval + AGU for misaligned transactions.  Do not update in case of
  // errors, mtval needs the (first) failing address.  Where an aligned access or the first half of
  // a misaligned access sees an error provide the calculated access address. For the second half of
  // a misaligned access provide the word aligned address of the second half.
  assign addr_last_d = addr_incr_req_o ? data_addr_w_aligned : data_addr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_last_q <= '0;
    end else if (addr_update) begin
      addr_last_q <= addr_last_d;
    end
  end

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext =  data_rdata_i[31:0];
      2'b01:   rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext =  data_rdata_i[31:0];
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

      default: rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
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

      default: rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    unique case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
      default:     data_rdata_ext = rdata_w_ext;
    endcase // case (data_type_q)
  end

  ///////////////////////////////
  // Read data integrity check //
  ///////////////////////////////

  // SEC_CM: BUS.INTEGRITY
  if (MemECC) begin : g_mem_rdata_ecc
    logic [1:0] ecc_err;
    logic [MemDataWidth-1:0] data_rdata_buf;

    prim_buf #(.Width(MemDataWidth)) u_prim_buf_instr_rdata (
      .in_i (data_rdata_i),
      .out_o(data_rdata_buf)
    );

    prim_secded_inv_39_32_dec u_data_intg_dec (
      .data_i     (data_rdata_buf),
      .data_o     (),
      .syndrome_o (),
      .err_o      (ecc_err)
    );

    // Don't care if error is correctable or not, they're all treated the same
    assign data_intg_err = |ecc_err;
  end else begin : g_no_mem_data_ecc
    assign data_intg_err = 1'b0;
  end

  /////////////
  // LSU FSM //
  /////////////

  // check for misaligned accesses that need to be split into two word-aligned accesses
  assign split_misaligned_access =
      ((lsu_type_i == 2'b00) && (data_offset != 2'b00)) || // misaligned word access
      ((lsu_type_i == 2'b01) && (data_offset == 2'b11));   // misaligned half-word access

  assign cpu_req_valid = lsu_req_i & ~((cheriot_enable_i == IbexMuBiOn) & lsu_cheriot_err_i);
  assign cpu_req_erred = lsu_req_i &  (cheriot_enable_i == IbexMuBiOn) & lsu_cheriot_err_i;

  // FSM
  always_comb begin
    ls_fsm_ns           = ls_fsm_cs;

    data_req_o          = 1'b0;
    addr_incr_req_o     = 1'b0;
    handle_misaligned_d = handle_misaligned_q;
    pmp_err_d           = pmp_err_q;
    lsu_err_d           = lsu_err_q;
    cheriot_err_d       = cheriot_err_q & (cheriot_enable_i == IbexMuBiOn);

    addr_update         = 1'b0;
    ctrl_update         = 1'b0;
    rdata_update        = 1'b0;

    perf_load_o         = 1'b0;
    perf_store_o        = 1'b0;

    lsu_go              = 1'b0;
    lsu_go_goodcap      = 1'b0;

    unique case (ls_fsm_cs)

      IDLE: begin
        pmp_err_d   = 1'b0;
        cheriot_err_d = 1'b0;

        if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) &
            cpu_req_erred) begin
          // cheriot access error: don't issue data_req; send error response back to WB stage
          data_req_o    = 1'b0;
          cheriot_err_d = 1'b1;
          ctrl_update   = 1'b1;         // update ctrl/address so we can report error correctly
          addr_update   = 1'b1;
          pmp_err_d     = 1'b0;
          lsu_err_d     = 1'b0;
          perf_load_o   = 1'b0;
          lsu_go        = 1'b1;         // decision to move forward with a request
          ls_fsm_ns     = IDLE;
        end else if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) &
            cpu_req_valid & lsu_is_cap_i) begin
          // normal cap access case
          data_req_o     = 1'b1;
          cheriot_err_d  = 1'b0;
          pmp_err_d      = data_pmp_err_i;
          lsu_err_d      = 1'b0;
          perf_load_o    = ~lsu_we_i;
          perf_store_o   = lsu_we_i;
          lsu_go         = 1'b1;         // decision to move forward with a request
          lsu_go_goodcap = 1'b1;

          if (data_gnt_i) begin
            ctrl_update = 1'b1;
            addr_update = 1'b1;
            ls_fsm_ns   = CTX_WAIT_GNT2;
          end else begin
            ls_fsm_ns   = CTX_WAIT_GNT1;
          end
        end else if (cpu_req_valid) begin
          // normal data access case
          data_req_o    = 1'b1;
          cheriot_err_d = 1'b0;
          pmp_err_d     = data_pmp_err_i;
          lsu_err_d     = 1'b0;
          perf_load_o   = ~lsu_we_i;
          perf_store_o  = lsu_we_i;
          lsu_go        = 1'b1;         // decision to move forward with a request

          if (data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
            handle_misaligned_d = split_misaligned_access;
            ls_fsm_ns           = split_misaligned_access ? WAIT_RVALID_MIS : IDLE;
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
          addr_update         = 1'b1;
          ctrl_update         = 1'b1;
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
          // Record the error status of the first part
          lsu_err_d = data_bus_err_i | pmp_err_q;
          // Capture the first rdata for loads
          rdata_update = ~data_we_q;
          // If already granted, wait for second rvalid
          ls_fsm_ns = data_gnt_i ? IDLE : WAIT_GNT;
          // Update the address for the second part, if no error
          addr_update = data_gnt_i & ~(data_bus_err_i | pmp_err_q);
          // clear handle_misaligned if second request is granted
          handle_misaligned_d = ~data_gnt_i;
        end else begin
          // first part rvalid is NOT received
          if (data_gnt_i) begin
            // second grant is received
            ls_fsm_ns = WAIT_RVALID_MIS_GNTS_DONE;
            handle_misaligned_d = 1'b0;
          end
        end
      end

      WAIT_GNT: begin
        // tell ID/EX stage to update the address
        addr_incr_req_o = handle_misaligned_q;
        data_req_o      = 1'b1;
        if (data_gnt_i || pmp_err_q) begin
          ctrl_update         = 1'b1;
          // Update the address, unless there was an error
          addr_update         = ~lsu_err_q;
          ls_fsm_ns           = IDLE;
          handle_misaligned_d = 1'b0;
        end
      end

      WAIT_RVALID_MIS_GNTS_DONE: begin
        // tell ID/EX stage to update the address (to make sure the
        // second address can be captured correctly for mtval and PMP checking)
        addr_incr_req_o = 1'b1;
        // Wait for the first rvalid, second request is already granted
        if (data_rvalid_i) begin
          // Update the pmp error for the second part
          pmp_err_d = data_pmp_err_i;
          // The first part cannot see a PMP error in this state
          lsu_err_d = data_bus_err_i;
          // Now we can update the address for the second part if no error
          addr_update = ~data_bus_err_i;
          // Capture the first rdata for loads
          rdata_update = ~data_we_q;
          // Wait for second rvalid
          ls_fsm_ns = IDLE;
        end
      end

      CTX_WAIT_GNT1: begin
        if (cheriot_enable_i == IbexMuBiOn) begin
          addr_incr_req_o = 1'b0;
          data_req_o      = 1'b1;
          if (data_gnt_i) begin
            ls_fsm_ns   = CTX_WAIT_GNT2;
            ctrl_update = 1'b1;
            addr_update = 1'b1;
          end
        end else begin
          ls_fsm_ns = IDLE;
        end
      end

      CTX_WAIT_GNT2: begin
        if (cheriot_enable_i == IbexMuBiOn) begin
          addr_incr_req_o = 1'b1;
          data_req_o      = 1'b1;
          if (data_gnt_i && (data_rvalid_i || (cap_rx_fsm_q == CRX_WAIT_RESP2))) begin
            ls_fsm_ns = IDLE;
          end else if (data_gnt_i) begin
            ls_fsm_ns = CTX_WAIT_RESP;
          end
        end else begin
          ls_fsm_ns = IDLE;
        end
      end

      CTX_WAIT_RESP: begin        // only needed if mem allows 2 active req
        if (cheriot_enable_i == IbexMuBiOn) begin
          addr_incr_req_o = 1'b1;
          data_req_o      = 1'b0;
          if (data_rvalid_i) begin
            ls_fsm_ns = IDLE;
          end
        end else begin
          ls_fsm_ns = IDLE;
        end
      end

      default: begin
        ls_fsm_ns = IDLE;
      end
    endcase
  end

  always_comb begin
    cap_rx_fsm_d = cap_rx_fsm_q;

    unique case (cap_rx_fsm_q)
      CRX_IDLE:
        if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) & lsu_go_goodcap)
          cap_rx_fsm_d = CRX_WAIT_RESP1;
      CRX_WAIT_RESP1:
        if (data_rvalid_i) cap_rx_fsm_d = CRX_WAIT_RESP2;
      CRX_WAIT_RESP2:
        if (data_rvalid_i && lsu_go_goodcap)
          cap_rx_fsm_d = CRX_WAIT_RESP1;
        else if (data_rvalid_i) cap_rx_fsm_d = CRX_IDLE;
      default: cap_rx_fsm_d = CRX_IDLE;
    endcase
  end

  // we assume ctrl will be held till req_done asserted
  // (once req captured in IDLE, it can be deasserted)
  logic lsu_req_done;

  assign lsu_req_done   = (lsu_go | (ls_fsm_cs != IDLE)) & (ls_fsm_ns == IDLE);
  assign lsu_req_done_o = lsu_req_done;

  // registers for FSM
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ls_fsm_cs           <= IDLE;
      handle_misaligned_q <= '0;
      pmp_err_q           <= '0;
      lsu_err_q           <= '0;
      resp_is_cap_q       <= 1'b0;
      resp_lc_clrperm_q   <= '0;
      cheriot_err_q       <= 1'b0;
      cap_rx_fsm_q        <= CRX_IDLE;
      cap_lsw_err_q       <= 1'b0;
      cap_lsw_data_q      <= '0;
      cap_lsw_tag_q       <= 1'b0;
    end else begin
      ls_fsm_cs           <= ls_fsm_ns;
      handle_misaligned_q <= handle_misaligned_d;
      pmp_err_q           <= pmp_err_d;
      lsu_err_q           <= lsu_err_d;
      cheriot_err_q       <= cheriot_err_d;

      cap_rx_fsm_q        <= cap_rx_fsm_d;

      // resp_is_cap_q aligns with responses on the data interface,
      // lsu_is_cap_i aligns with requests
      //   we use lsu_go to qualify this update
      //   - note this implies that LSU only support a outstand request at a time
      //   - new request can't be issued (go) until resp_valid
      //   - also note resp_valid is gated by (ls_fsm_cs == IDLE)
      if (lsu_go) begin
        resp_is_cap_q     <= lsu_is_cap_i;
        resp_lc_clrperm_q <= lsu_lc_clrperm_i;
      end

      if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) &&
          (cap_rx_fsm_q == CRX_WAIT_RESP1) && data_rvalid_i && (~data_we_q)) begin
        cap_lsw_data_q <= data_rdata_i[31:0];
        cap_lsw_tag_q  <= data_tag_i;
      end

      if ((BaseIsa == BaseIsaRV32IorCHERIoT) & (cheriot_enable_i == IbexMuBiOn) &&
          (cap_rx_fsm_q == CRX_WAIT_RESP1) && data_rvalid_i) begin
        cap_lsw_err_q <= data_bus_err_i;
      end

    end
  end

  /////////////
  // Outputs //
  /////////////

  logic all_resp;
  assign data_or_pmp_err    = lsu_err_q | data_bus_err_i | pmp_err_q |
                              ((cheriot_enable_i == IbexMuBiOn) &
                               (cheriot_err_q | (resp_is_cap_q & cap_lsw_err_q)));

  assign all_resp           = data_rvalid_i | pmp_err_q |
                              ((cheriot_enable_i == IbexMuBiOn) & cheriot_err_q);
  assign lsu_resp_valid_o   = all_resp & (ls_fsm_cs == IDLE);

  // this goes to wb as rf_we_lsu, so needs to be gated when data needs to go back to EX
  assign lsu_rdata_valid_o  = (ls_fsm_cs == IDLE) & data_rvalid_i & ~data_or_pmp_err & ~data_we_q &
                              ~data_intg_err;

  // output to register file
  if (BaseIsa == BaseIsaRV32IorCHERIoT) begin : gen_memcap_rd
    assign lsu_rdata_o = ((cheriot_enable_i == IbexMuBiOn) & resp_is_cap_q) ?
                         cap_lsw_data_q : data_rdata_ext;
    assign lsu_rcap_o  = ((cheriot_enable_i == IbexMuBiOn) && resp_is_cap_q &&
                          data_rvalid_i && (cap_rx_fsm_q == CRX_WAIT_RESP2) &&
                          (~data_or_pmp_err)) ?
                         cheriot_mem_to_cap({data_tag_i, data_rdata_i[31:0]},
                             {cap_lsw_tag_q, cap_lsw_data_q}, resp_lc_clrperm_q) :
                         NULL_CAP;
  end else begin : gen_no_cap_rd
    assign lsu_rdata_o = data_rdata_ext;
    assign lsu_rcap_o  = NULL_CAP;
    logic unused_cap_rd_sigs;
    assign unused_cap_rd_sigs = ^{resp_lc_clrperm_q, cap_lsw_data_q, cap_lsw_tag_q, data_tag_i};
  end


  // output data address must be word aligned
  assign data_addr_w_aligned = {data_addr[31:2], 2'b00};

  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;
  assign data_we_o     = lsu_we_i;
  assign data_be_o     = data_be;

  /////////////////////////////////////
  // Write data integrity generation //
  /////////////////////////////////////

  // SEC_CM: BUS.INTEGRITY
  if (MemECC) begin : g_mem_wdata_ecc
    prim_secded_inv_39_32_enc u_data_gen (
      .data_i (data_wdata_data),
      .data_o (data_wdata_o)
    );
  end else begin : g_no_mem_wdata_ecc
    assign data_wdata_o = data_wdata_data;
  end

  assign data_tag_o = data_wdata_tag;

  // output to ID stage: mtval + AGU for misaligned transactions
  assign addr_last_o = addr_last_q;

  // Signal a load or store error depending on the transaction type outstanding
  assign load_err_o  = data_or_pmp_err & ~data_we_q & lsu_resp_valid_o;
  assign store_err_o = data_or_pmp_err &  data_we_q & lsu_resp_valid_o;
  // Integrity errors are their own category for timing reasons. load_err_o is factored directly
  // into data_req_o to enable synchronous exception on load errors without performance loss (An
  // upcoming load cannot request until the current load has seen its response, so the earliest
  // point the new request can be sent is the same cycle the response is seen). If load_err_o isn't
  // factored into data_req_o there would have to be a stall cycle between all back to back loads.
  // The data_intg_err signal is generated combinatorially from the incoming data_rdata_i. Were it
  // to be factored into load_err_o there would be a feedthrough path from data_rdata_i to
  // data_req_o which is undesirable.
  assign load_resp_intg_err_o  = data_intg_err & data_rvalid_i & ~data_we_q;
  assign store_resp_intg_err_o = data_intg_err & data_rvalid_i & data_we_q;

  // Send to controller for mcause encoding.
  assign lsu_err_is_cheriot_o  = (cheriot_enable_i == IbexMuBiOn) & cheriot_err_q;

  assign busy_o = (ls_fsm_cs != IDLE);

  //////////
  // FCOV //
  //////////
`ifndef DV_FCOV_DISABLE
  // Set when awaiting the response for the second half of a misaligned access
  logic fcov_mis_2_en_d, fcov_mis_2_en_q;

  // fcov_mis_rvalid_1: Set when the response is received to the first half of a misaligned access,
  // fcov_mis_rvalid_2: Set when response is received for the second half
  logic fcov_mis_rvalid_1, fcov_mis_rvalid_2;

  // Set when the first half of a misaligned access saw a bus error
  logic fcov_mis_bus_err_1_d, fcov_mis_bus_err_1_q;

  assign fcov_mis_rvalid_1 = ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE} &&
                                data_rvalid_i;

  assign fcov_mis_rvalid_2 = ls_fsm_cs inside {IDLE} && fcov_mis_2_en_q && data_rvalid_i;

  assign fcov_mis_2_en_d = fcov_mis_rvalid_2 ? 1'b0            :  // clr
                           fcov_mis_rvalid_1 ? 1'b1            :  // set
                                               fcov_mis_2_en_q ;

  assign fcov_mis_bus_err_1_d = fcov_mis_rvalid_2                   ? 1'b0                 : // clr
                                fcov_mis_rvalid_1 && data_bus_err_i ? 1'b1                 : // set
                                                                      fcov_mis_bus_err_1_q ;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fcov_mis_2_en_q <= 1'b0;
      fcov_mis_bus_err_1_q <= 1'b0;
    end else begin
      fcov_mis_2_en_q <= fcov_mis_2_en_d;
      fcov_mis_bus_err_1_q <= fcov_mis_bus_err_1_d;
    end
  end
`endif

  `DV_FCOV_SIGNAL(logic, ls_error_exception, (load_err_o | store_err_o) & ~pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_pmp_exception, (load_err_o | store_err_o) & pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_first_req, lsu_req_i & (ls_fsm_cs == IDLE))
  `DV_FCOV_SIGNAL(logic, ls_second_req,
    (ls_fsm_cs inside {WAIT_RVALID_MIS}) & data_req_o & addr_incr_req_o)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_1,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_GNT_MIS}) && pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_2,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE}) && data_pmp_err_i)

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexDataTypeKnown, (lsu_req_i | busy_o) |-> !$isunknown(lsu_type_i))
  `ASSERT(IbexDataOffsetKnown, (lsu_req_i | busy_o) |-> !$isunknown(data_offset))
  `ASSERT_KNOWN(IbexRDataOffsetQKnown, rdata_offset_q)
  `ASSERT_KNOWN(IbexDataTypeQKnown, data_type_q)
  `ASSERT(IbexLsuStateValid, ls_fsm_cs inside {
      IDLE, WAIT_GNT_MIS, WAIT_RVALID_MIS, WAIT_GNT,
      WAIT_RVALID_MIS_GNTS_DONE,
      CTX_WAIT_GNT1, CTX_WAIT_GNT2, CTX_WAIT_RESP})

  // Address must not contain X when request is sent.
  `ASSERT(IbexDataAddrUnknown, data_req_o |-> !$isunknown(data_addr_o))

  // Address must be word aligned when request is sent.
  `ASSERT(IbexDataAddrUnaligned, data_req_o |-> (data_addr_o[1:0] == 2'b00))

  // CHERIoT isolation: when CHERIoT is disabled, capability-specific inputs must be 0.
  `ASSERT_IF(IbexLsuIsCapDisabled,    !lsu_is_cap_i,       cheriot_enable_i != IbexMuBiOn)
  `ASSERT_IF(IbexLsuCheriotErrDisabled, !lsu_cheriot_err_i, cheriot_enable_i != IbexMuBiOn)

endmodule
