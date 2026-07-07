// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheriot_rmw_filter
  import cheriot_pkg::*;
#(
  // TL-UL address type
  parameter type   addr_t              = logic [top_pkg::TL_AW-1:0],
  parameter addr_t MainSramBaseAddr    = 'h0,
  parameter addr_t MainSramTopAddr     = 'h0,
  parameter addr_t NvmBaseAddr         = 'h0,
  parameter addr_t NvmTopAddr          = 'h0,
  parameter addr_t MetaMainSramTagBase = 'h0,
  parameter addr_t MetaNvmTagBase      = 'h0
) (
  input  logic clk_i,
  input  logic rst_ni,

  // Host port
  input  tlul_pkg::tl_h2d_t tl_h_i,
  input  logic              tag_h_i,
  output tlul_pkg::tl_d2h_t tl_h_o,
  output logic              tag_h_o,

  // Device port
  output tlul_pkg::tl_h2d_t tl_d_o,
  input  tlul_pkg::tl_d2h_t tl_d_i,

  // Error signals
  output logic data_intg_error_o,
  output logic rsp_intg_error_o,
  output logic device_error_o
);

  ///////////
  // Types //
  ///////////

  // The padding to 57 bit of the BM response fields subject to ECC
  localparam int unsigned RspIntgPadding = tlul_pkg::D2HRspMaxWidth -
                                           $bits(tlul_pkg::tl_d2h_rsp_intg_t);

  typedef enum logic [1:0] {
    Passthrough  = 2'h0,
    Fill         = 2'h1,
    WriteBackReq = 2'h2,
    WriteBackAck = 2'h3
  } bit_rmw_state_e;

  typedef struct packed {
    logic [31:8] meta_word;
    logic  [7:3] bit_sel;
    logic  [2:0] rsvd;
  } meta_addr_t;


  /////////////
  // Signals //
  /////////////

  bit_rmw_state_e state_d, state_q;

  // Signals concerning the multiplexing of the TL-UL H2D requests
  logic forward_r_req;
  logic emit_r_req;
  logic emit_w_req;

  // Signals concerning the multiplexing of the TL-UL H2D responses
  logic ack_fill;
  logic ack_skip;
  logic ack_write_back;

  // We need to keep track of ongoing reads
  logic is_read_d, is_read_q;

  // We need to store the address of the access
  meta_addr_t meta_addr_d, meta_addr_q;

  // Remapped address
  meta_addr_t addr_sel, addr_stem, addr_remap;

  // Unused address signals
  logic unused_addr;

  // We need to store whether a capability write had a valid tag bit
  logic tag_q;

  // We need to store the word read before writing it back modified
  logic [31:0] word_q;

  // Helper signals
  logic skip_write_back;
  logic update_word;

  // Device response ECC signals
  tlul_pkg::tl_d2h_rsp_intg_t rsp_intg;
  logic [1:0]                 rsp_intg_error;
  logic [1:0]                 rsp_data_intg_error;


  ////////////////////
  // Helper Signals //
  ////////////////////

  // We assign the address to an internally defined packed struct to gain access to its fields.
  assign meta_addr_d     = tl_h_i.a_address;
  // We can skip the write back operation if the tag to be written matches the current state
  assign skip_write_back = tl_d_i.d_data[meta_addr_q.bit_sel] == tag_q;


  /////////////////
  // Control FSM //
  /////////////////

  always_comb begin : proc_rwm_fsm

    // state stays stable
    state_d        = state_q;

    forward_r_req  = 1'b0;
    emit_r_req     = 1'b0;
    emit_w_req     = 1'b0;

    ack_fill       = 1'b0;
    ack_skip       = 1'b0;
    ack_write_back = 1'b0;

    is_read_d      = 1'b0;
    update_word    = 1'b0;

    unique case(state_q)

      // The pass-through state allows reads to just be forwarded. Should a properly handshaked
      // write arrive request pass, we switch to the Fill state.
      Passthrough: begin
        if(tl_h_i.a_opcode == tlul_pkg::PutFullData ||
           tl_h_i.a_opcode == tlul_pkg::PutPartialData) begin
          emit_r_req = 1'b1;
          if(tl_h_i.a_valid && tl_h_o.a_ready) begin
            state_d = Fill;
          end
        end else if(tl_h_i.a_opcode == tlul_pkg::Get) begin
          forward_r_req = 1'b1;
          is_read_d     = 1'b1;
        end
      end

      // In fill, we check whether the read data matches the capability bit we intend to write. If
      // so, we can omit the write back and return back to pass-through. If not, we have to do
      // the modification followed by the write back.
      Fill: begin
        if(tl_d_i.d_valid) begin
          // We don't have to do anything more
          if(skip_write_back) begin
            ack_skip = 1'b1;
            if(tl_h_i.d_ready) begin
              state_d = Passthrough;
            end
          // An update of the SRAM state is required
          end else begin
            ack_fill    = 1'b1;
            update_word = 1'b1;
            state_d     = WriteBackReq;
          end
        end
      end

      // We emit a write request towards the device carrying the updated state.
      WriteBackReq: begin
        emit_w_req = 1'b1;
        if(tl_d_i.a_ready) begin
          state_d = WriteBackAck;
        end
      end

      // We acknowledge the write response from the device and forward it to the host. We are now
      // done with the RWM operation and can return to pass-through.
      WriteBackAck: begin
        ack_write_back = 1'b1;
        if(tl_d_i.d_valid && tl_h_i.d_ready) begin
          state_d = Passthrough;
        end
      end

      default:;
    endcase
  end

  // An enable-FF storing the meta data. This state is updated whenever the host gets a
  // request handshaked.
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_request_meta_store
    if(!rst_ni) begin
      meta_addr_q <= '0;
      tag_q       <= 1'b0;
    end else begin
      if (tl_h_i.a_valid && tl_h_o.a_ready) begin
        meta_addr_q <= meta_addr_d;
        tag_q       <= tag_h_i;
      end
    end
  end

  // This enable FF, stores the current state before the modification in the fill state should an
  // update be required.
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_word_store
    if(!rst_ni) begin
      word_q <= '0;
    end else begin
      if (update_word) begin
        word_q <= tl_d_i.d_data;
      end
    end
  end

  // This synchronously clearable, enable FF, stores the state of an ongoing read transaction.
  // If clears the state on every completed ack towards the host. It is set on handshaking a
  // host read request.
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_read_ongoing_flop
    if(!rst_ni) begin
      is_read_q <= 1'b0;
    end else begin
      if (tl_h_o.d_valid && tl_h_i.d_ready) begin
        is_read_q <= 1'b0;
      end else if (tl_h_i.a_valid && tl_h_o.a_ready) begin
        is_read_q <= is_read_d;
      end
    end
  end

  // The state can be updated every cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_fsm_state_store
    if(!rst_ni) begin
      state_q <= Passthrough;
    end else begin
      state_q <= state_d;
    end
  end


  /////////////////////
  // TL Multiplexing //
  /////////////////////

  // This process is really crammed as a side effect of bundling handshaking and (meta) data signals
  // in a single request and response struct. We thus combine here handshaking and data
  // multiplexing.
  always_comb begin : proc_tl_muxing

    // Default pass-through for all transport signals (except handshaking)
    tl_h_o  = tl_d_i;
    tl_d_o  = tl_h_i;

    // Invalid capability as a default
    tag_h_o = 1'b0;

    // Inert handshaking is the default
    tl_h_o.d_valid = 1'b0;
    tl_d_o.a_valid = 1'b0;
    tl_h_o.a_ready = 1'b0;
    tl_d_o.d_ready = 1'b0;

    // In the case of a read, we just forward the request. We only modify the address to
    // point to the word in meta memory holding the capability.
    if(forward_r_req) begin
      // We are in pass-through case and a request arrives -> we forward it
      // but we ensure we divide the address by 64 as one request can track 32
      // capabilities or 64 words.
      tl_d_o.a_address       = addr_remap;
      // Recalculate the command integrity as we have modified the address
      tl_d_o.a_user.cmd_intg = tlul_pkg::get_cmd_intg(tl_d_o);
      tl_d_o.a_valid         = tl_h_i.a_valid;
      tl_h_o.a_ready         = tl_d_i.a_ready;

    // In the case of a write, we first emit a word read towards meta memory, by forwarding
    // a the modified upstream write request, to check whether the corresponding
    // capability tag is set.
    end else if(emit_r_req) begin
      tl_d_o                  = tlul_pkg::TL_H2D_DEFAULT;
      tl_d_o.a_address        = addr_remap;
      tl_d_o.a_opcode         = tlul_pkg::Get;
      tl_d_o.a_size           = 'd2;
      tl_d_o.a_user.cmd_intg  = tlul_pkg::get_cmd_intg(tl_d_o);
      tl_d_o.a_user.data_intg = tlul_pkg::get_data_intg(tl_d_o.a_data);
      tl_d_o.a_valid          = tl_h_i.a_valid;
      tl_h_o.a_ready          = tl_d_i.a_ready;

    // In the case of a write that modifies state, we eventually need to emit a new write. Here we
    // don't have to handshake the upstream host request interface.
    end else if(emit_w_req) begin
      tl_d_o                             = tlul_pkg::TL_H2D_DEFAULT;
      tl_d_o.a_address                   = addr_remap;
      tl_d_o.a_opcode                    = tlul_pkg::PutFullData;
      tl_d_o.a_size                      = 'd2;
      tl_d_o.a_mask                      = '1;
      tl_d_o.a_data                      = word_q;
      tl_d_o.a_data[meta_addr_q.bit_sel] = tag_q;
      tl_d_o.a_user.cmd_intg             = tlul_pkg::get_cmd_intg(tl_d_o);
      tl_d_o.a_user.data_intg            = tlul_pkg::get_data_intg(tl_d_o.a_data);
      tl_d_o.a_valid                     = 1'b1;
    end

    // In the read case, we return the read response. The corresponding capability tag bit is
    // placed on the host's output tag interface.
    if(is_read_q) begin
      tl_h_o.d_valid  = tl_d_i.d_valid;
      tl_d_o.d_ready  = tl_h_i.d_ready;
      tag_h_o         = tl_d_i.d_data[meta_addr_q.bit_sel] && !tl_d_i.d_error;

    // We have translated a write request into a read request to inquire the state of the
    // tag word. Checking the capability bit, we notice that we don't have to perform an update.
    // We thus translate the read response from the meta device into a write response.
    end else if(ack_skip) begin
      tl_h_o.d_opcode = tlul_pkg::AccessAck;
      tl_d_o.d_ready  = tl_h_i.d_ready;
      tl_h_o.d_valid  = 1'b1;

    // When performing a fill and update, we need to acknowledge the downstream device transaction
    // without acknowledging the host's response.
    end else if(ack_fill) begin
      tl_d_o.d_ready  = 1'b1;

    // A write back answer arrives from the device; we forward this to the host.
    end else if(ack_write_back) begin
      tl_h_o.d_valid  = tl_d_i.d_valid;
      tl_d_o.d_ready  = tl_h_i.d_ready;
    end
  end


  ///////////////////////////
  // Response ECC Checking //
  ///////////////////////////

  // Did we receive a device error?
  assign device_error_o = tl_d_i.d_valid && tl_d_o.d_ready && tl_d_i.d_error;

  // Get the response fields subject to ECC
  assign rsp_intg = tlul_pkg::extract_d2h_rsp_intg(tl_d_i);

  // Check the bitmap response integrity
  prim_secded_inv_64_57_dec u_prim_secded_inv_64_57_dec_rsp (
    .data_i    ({tl_d_i.d_user.rsp_intg, {RspIntgPadding{1'b0}}, rsp_intg}),
    .data_o    (/*Not Connected*/),
    .syndrome_o(/*Not Connected*/),
    .err_o     (rsp_intg_error)
  );

  // Mask response integrity error if response is not being handshaked
  assign rsp_intg_error_o = tl_d_i.d_valid && tl_d_o.d_ready && (|rsp_intg_error);

  // Check the device response data integrity
  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_rsp_data (
    .data_i    ({tl_d_i.d_user.data_intg, tl_d_i.d_data}),
    .data_o    (/*Not Connected*/),
    .syndrome_o(/*Not Connected*/),
    .err_o     (rsp_data_intg_error)
  );

  // Mask response integrity error if response is not being handshaked
  assign data_intg_error_o = tl_d_i.d_valid && tl_d_o.d_ready && (|rsp_data_intg_error);


  ///////////////////////
  // Address Remapping //
  ///////////////////////

  always_comb begin: proc_address_remap
    // defaults (only happen if something goes wrong, we map to address 0 which should not be
    // mapped to anything)
    addr_sel   = '0;
    addr_stem  = '0;
    addr_remap = '0;

    // select either the address of the currently active host request or the stored value
    if(forward_r_req || emit_r_req) begin
      addr_sel = meta_addr_d;
    end else if(emit_w_req) begin
      addr_sel = meta_addr_q;
    end

    // remap address
    if(addr_sel >= MainSramBaseAddr && addr_sel < MainSramTopAddr) begin
      addr_stem  = addr_sel - MainSramBaseAddr;
      addr_remap = MetaMainSramTagBase + (addr_stem.meta_word << 32'd2);
    end else if(addr_sel >= NvmBaseAddr && addr_sel < NvmTopAddr) begin
      addr_stem  = addr_sel - NvmBaseAddr;
      addr_remap = MetaNvmTagBase + (addr_stem.meta_word << 32'd2);
    end
  end

  assign unused_addr = ^{addr_stem.bit_sel, addr_stem.rsvd};

endmodule
