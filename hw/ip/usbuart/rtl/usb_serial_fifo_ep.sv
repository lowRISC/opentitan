// Copyright lowRISC contributors.
// Copyright Luke Valenty (TinyFPGA project)
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module usb_serial_fifo_ep  #(
  parameter int unsigned MaxPktSizeByte = 32,

  // Derived parameters
  localparam int unsigned PktW = $clog2(MaxPktSizeByte)
) (
  input               clk_i,
  input               rst_ni,

  // out endpoint interface
  input               out_ep_data_put_i,
  input [PktW - 1:0]  out_ep_put_addr_i,
  input [7:0]         out_ep_data_i,
  input               out_ep_acked_i,
  input               out_ep_rollback_i,
  input               out_ep_setup_i,
  output logic        out_ep_full_o,
  output logic        out_ep_stall_o,

  // in endpoint interface
  input               in_ep_rollback_i,
  input               in_ep_acked_i,
  input [PktW - 1:0]  in_ep_get_addr_i,
  input               in_ep_data_get_i,
  output logic        in_ep_stall_o,
  output logic        in_ep_has_data_o,
  output logic [7:0]  in_ep_data_o,
  output logic        in_ep_data_done_o,

  // fifo interface
  input               tx_empty,
  input               rx_full,
  output logic        tx_read,
  output logic        rx_write,
  output logic        rx_err, // Signals fifo overflow
  output logic [7:0]  rx_fifo_wdata,
  input [7:0]         tx_fifo_rdata,

  // information
  output logic [15:0] baud_o,
  output logic [1:0]  parity_o
);

  logic                do_setup;
  logic [7:0]          in_setup_data;
  logic                in_setup_has_data, in_setup_data_done;

  assign out_ep_stall_o = 1'b0;
  assign in_ep_stall_o = 1'b0;

  // suppress errors
  logic                unused_1;
  assign unused_1 = in_ep_rollback_i;

  ////////////////////////////////////////
  // OUT endpoint (from usb to rx_fifo) //
  ////////////////////////////////////////

  // In future probably better to eliminate this buffer and add rollback to async FIFO
  // Will receive the 2 bytes of CRC, so may get MAX_PACKET_SIZE+2 bytes
  logic [7:0] out_pkt_buffer [MaxPktSizeByte];
  logic [PktW - 1:0] ob_rptr;
  logic [PktW:0]     ob_max_used;
  logic          ob_unload;

  always_ff @(posedge clk_i) begin
    if (!do_setup && out_ep_data_put_i && !ob_unload) begin
      // don't write if the address has wrapped (happens for two CRC bytes after max data)
      if (!ob_max_used[PktW]) begin
        out_pkt_buffer[out_ep_put_addr_i] <= out_ep_data_i;
      end
      // In the normal case <MAX_PACKET_SIZE this is ob_max_used <= out_ep_put_addr_i
      // Following all ones ob_max_used will get 1,00..00 and 1,00..01 to cover
      // one and two bytes of the CRC overflowing, then stick at 1,00..01
      ob_max_used[0] <= (ob_max_used[PktW] & ob_max_used[0]) ? 1'b1 : out_ep_put_addr_i[0];
      ob_max_used[PktW - 1: 1] <= ob_max_used[PktW] ? 0 : out_ep_put_addr_i[PktW - 1:1];
      ob_max_used[PktW] <= (&ob_max_used[PktW - 1:0]) | ob_max_used[PktW];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ob_unload <= 1'b0;
    end else begin
      if (!do_setup && out_ep_acked_i) begin
        ob_unload <= 1'b1;
      end else if (({1'b0, ob_rptr} == (ob_max_used - {1'b0, PktW'(2)})) && !rx_full) begin
        ob_unload <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ob_rptr <= '0;
      rx_write <= 1'b0;
    end else begin
      if (!ob_unload) begin
        ob_rptr <= '0;
        rx_write <= 1'b0;
      end else if (!rx_full) begin // implicit && ob_unload
        rx_write <= 1'b1;
        rx_fifo_wdata <= out_pkt_buffer[ob_rptr];
        ob_rptr <= ob_rptr + 1'b1;
      end else begin
        rx_write <= 1'b0;
      end
    end
  end

  // rx_err indicates data loss prior to item it is attached to
  // won't do that here, backpressure the usb instead
  assign rx_err = 1'b0;

  // ob should unload in 32 cycles i.e. 32/4 = 8 bit times, so this will only
  // happen if the FIFO really gets full
  assign out_ep_full_o = ~do_setup && ob_unload;

  ///////////////////////////////////////
  // IN endpoint (from tx_fifo to usb) //
  ///////////////////////////////////////

  // packet buffer to allow rollback in the case of a NAK
  logic [7:0]    in_pkt_buffer [MaxPktSizeByte];
  logic [PktW:0] pb_wptr;
  logic          pb_freeze, pb_done;
  logic [7:0]    pb_rdata;

  // Should be ok to flop this if it needs it for timing
  assign pb_rdata = in_pkt_buffer[in_ep_get_addr_i];
  // The protocol engine will finish the packet if it is max length
  assign pb_done = !do_setup && (pb_wptr != '0) && ({1'b0, in_ep_get_addr_i} == pb_wptr);

  assign in_ep_data_o      = do_setup ? in_setup_data      : pb_rdata;
  assign in_ep_data_done_o = do_setup ? in_setup_data_done : pb_done;
  assign in_ep_has_data_o  = do_setup ? in_setup_has_data  : (pb_wptr != '0);

  // In the case of a NAK must resubmit exactly the same packet
  // So freeze the buffer to prevent any additional writes
  // Since this stops movement of the pb_wptr and the PE will stop moving the get_addr
  // it is just a copy of pb_done (if the second stops being true need the always_ff)
  assign pb_freeze = pb_done;

  //always_ff @(posedge clk_i or negedge rst_ni) begin
  //  if (!rst_ni) begin
  //    pb_freeze <= 0;
  //  end else begin
  //    if (pb_done && ~in_ep_acked_i) begin
  //      pb_freeze <= 1;
  //    end else if (~do_setup && in_ep_acked_i) begin
  //      pb_freeze <= 0;
  //    end
  //  end
  //end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tx_read <= 0;
    end else begin
      // Limits to every other cycle, but that is still ((4/2)*8) = 16* line byte rate
      tx_read <= !tx_read && !tx_empty && !pb_done && !pb_freeze && !pb_wptr[PktW];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pb_wptr <= '0;
    end else begin
      if (tx_read) begin
        in_pkt_buffer[pb_wptr[PktW - 1:0]] <= tx_fifo_rdata;
        pb_wptr <= pb_wptr + 1'b1;
      end else if (!do_setup && in_ep_acked_i) begin
        pb_wptr <= '0;
      end
    end
  end

  ////////////////////////////////////////////////
  // SETUP endpoint (configure baud and parity) //
  ////////////////////////////////////////////////

  // State machine for control transfers
  typedef enum logic [2:0] {
    StIdle      = 3'h0,
    StSetup     = 3'h1,
    StDataIn    = 3'h2,
    StDataOut   = 3'h3,
    StStatusIn  = 3'h4,
    StStatusOut = 3'h5
  } state_ctrl_xfr_e;

  state_ctrl_xfr_e ctrl_xfr_state;
  state_ctrl_xfr_e ctrl_xfr_state_next;
  logic setup_stage_end;
  logic status_stage_end;
  logic send_zero_length_data_pkt;

  // keep track of new out data start and end
  logic pkt_start;
  logic pkt_end;

  // Record the 8 bytes of setup data
  // setup_data_addr[3] protects in case of overlong packet
  logic [7:0] bmRequestType, raw_setup_data [8];
  // Alias for the setup bytes using names from USB spec
  logic [7:0] bRequest;
  logic [15:0] wValue, wLength, wIndex;

  assign pkt_start = (out_ep_put_addr_i == '0) && out_ep_data_put_i;
  assign pkt_end = out_ep_acked_i || out_ep_rollback_i;

  logic setup_pkt_start, has_data_stage, out_data_stage, in_data_stage;
  assign do_setup = setup_pkt_start || (ctrl_xfr_state != StIdle);
  assign setup_pkt_start = pkt_start && out_ep_setup_i;
  assign has_data_stage = wLength != 16'h0;
  assign out_data_stage = has_data_stage && !bmRequestType[7];
  assign in_data_stage = has_data_stage && bmRequestType[7];

  logic [1:0] bytes_sent;
  logic [1:0] send_length;
  logic all_data_sent, more_data_to_send, in_data_transfer_done;

  // if any upper bits in wLength are set the send_length will trigger first
  // second check only covers wLength=0 or 1.
  assign all_data_sent = (bytes_sent >= send_length) ||
                         (bytes_sent >= {|wLength[15:1], wLength[0]});
  assign more_data_to_send = !all_data_sent;

  rising_edge_detector detect_in_data_transfer_done (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .in_i  (all_data_sent),
    .out_o (in_data_transfer_done)
  );

  assign in_setup_has_data = more_data_to_send || send_zero_length_data_pkt;
  assign in_setup_data_done = (in_data_transfer_done && (ctrl_xfr_state == StDataIn)) ||
                              send_zero_length_data_pkt;


  ////////////////////////////////////
  // control transfer state machine //
  ////////////////////////////////////

  always_comb begin
    setup_stage_end = 1'b0;
    status_stage_end = 1'b0;
    send_zero_length_data_pkt = 1'b0;

    unique case (ctrl_xfr_state)
      StIdle: begin
        if (setup_pkt_start) begin
          ctrl_xfr_state_next = StSetup;
        end else begin
          ctrl_xfr_state_next = StIdle;
        end
      end

      StSetup: begin
        if (pkt_end) begin
          // rollback here is most likely a CRC error on the SETUP packet
          if (out_ep_rollback_i) begin
            ctrl_xfr_state_next = StIdle;
          end else if (in_data_stage) begin
            ctrl_xfr_state_next = StDataIn;
            setup_stage_end = 1'b1;
          end else if (out_data_stage) begin
            ctrl_xfr_state_next = StDataOut;
            setup_stage_end = 1'b1;
          end else begin
            ctrl_xfr_state_next = StStatusIn;
            send_zero_length_data_pkt = 1'b1;
            setup_stage_end = 1'b1;
          end
        end else begin
          ctrl_xfr_state_next = StSetup;
        end // else: !if(pkt_end)
      end // case: SETUP

      StDataIn: begin
        //No error states that would be signalled with in_ep_stall
        if (in_ep_acked_i && all_data_sent) begin
          ctrl_xfr_state_next = StStatusOut;
        end else begin
          ctrl_xfr_state_next = StDataIn;
        end
      end

      StDataOut: begin
        if (out_ep_acked_i) begin
          ctrl_xfr_state_next = StStatusIn;
          send_zero_length_data_pkt = 1'b1;
        end else begin
          ctrl_xfr_state_next = StDataOut;
        end
      end

      StStatusIn: begin
        if (in_ep_acked_i) begin
          ctrl_xfr_state_next = StIdle;
          status_stage_end = 1'b1;
        end else begin
          ctrl_xfr_state_next = StStatusIn;
          send_zero_length_data_pkt = 1'b1;
        end
      end

      StStatusOut: begin
        if (out_ep_acked_i) begin
          ctrl_xfr_state_next = StIdle;
          status_stage_end = 1'b1;
        end else begin
          ctrl_xfr_state_next = StStatusOut;
        end
      end

      default begin
        ctrl_xfr_state_next = StIdle;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_xfr_state <= StIdle;
    end else begin
      ctrl_xfr_state <= ctrl_xfr_state_next;
    end
  end

  assign bmRequestType = raw_setup_data[0];
  assign bRequest = raw_setup_data[1];
  assign wValue = {raw_setup_data[3][7:0], raw_setup_data[2][7:0]};
  assign wIndex = {raw_setup_data[5][7:0], raw_setup_data[4][7:0]};
  assign wLength = {raw_setup_data[7][7:0], raw_setup_data[6][7:0]};

  // Suppress warnings
  logic [6:0]  unused_bmR;
  logic [15:0] unused_wIndex;
  assign unused_bmR = bmRequestType[6:0];
  assign unused_wIndex = wIndex;

  // Check of upper put_addr bits needed because CRC will be sent (10 bytes total)
  always_ff @(posedge clk_i) begin
    if (out_ep_setup_i && out_ep_data_put_i && (out_ep_put_addr_i[PktW - 1:3] == 0)) begin
      raw_setup_data[out_ep_put_addr_i[2:0]] <= out_ep_data_i;
    end
  end

  // Send setup data (which will be empty in case of a SET operation)
  // Tried to optimize by reusing the raw_setup_data storage but
  // it seems hard to do that and meet style of only assign in one always_ff
  // and only use if/else so 16 extra flops
  logic [15:0] return_data;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      baud_o <= 16'd1152; // spec is default to 115,200 baud
      parity_o <= 1'b0;   // with no parity
      bytes_sent <= '0;
      send_length <= '0;
      return_data <= '0;
    end else begin
      if (setup_stage_end) begin
        bytes_sent <= '0;
        // Command (bRequest) comes from Google Simple Serial Stream spec
        // so no standard defines for the codes
        // (note looks like this is the first time REQ has been implemented)
        unique case (bRequest)
          8'h00: begin
            // REQ_PARITY
            return_data <= {14'b0, parity_o};
            send_length <= 2'b10;
          end

          8'h01: begin
            // SET_PARITY
            send_length <= 2'b00;
            parity_o    <= wValue[1:0];
          end

          8'h02: begin
            // REQ_BAUD
            return_data <= baud_o;
            send_length <= 2'b10;
          end

          8'h03: begin
            // SET_BAUD
            send_length <= 2'b00;
            baud_o      <= wValue;
          end
          default begin
            send_length <= 2'b00;
          end
        endcase
      end else if ((ctrl_xfr_state == StDataIn) && more_data_to_send && in_ep_data_get_i) begin
        bytes_sent <= bytes_sent + 2'b01;
      end else if (status_stage_end) begin
        bytes_sent <= '0;
      end
    end // else: !if(!rst_ni)
  end
  assign in_setup_data = bytes_sent[0] ? return_data[15:8] : return_data[7:0];

endmodule
