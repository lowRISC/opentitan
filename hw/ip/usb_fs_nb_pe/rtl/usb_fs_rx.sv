// Copyright lowRISC contributors.
// Copyright ETH Zurich.
// Copyright Luke Valenty (TinyFPGA project, https://github.com/tinyfpga/TinyFPGA-Bootloader).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module usb_fs_rx (
  // A 48MHz clock is required to recover the clock from the incoming data.
  input  logic clk_i,
  input  logic rst_ni,
  input  logic link_reset_i,

  // configuration
  input  logic cfg_eop_single_bit_i,
  input  logic cfg_rx_differential_i,

  // USB data+ and data- lines (synchronous)
  input  logic usb_d_i,
  input  logic usb_dp_i,
  input  logic usb_dn_i,

  // Transmit enable disables the receier
  input  logic tx_en_i,

  // pulse on every bit transition.
  output logic bit_strobe_o,

  // Pulse on beginning of new packet.
  output logic pkt_start_o,

  // Pulse on end of current packet.
  output logic pkt_end_o,

  // Most recent packet decoded.
  output logic [3:0]  pid_o,
  output logic [6:0]  addr_o,
  output logic [3:0]  endp_o,
  output logic [10:0] frame_num_o,

  // Pulse on valid data on rx_data.
  output logic rx_data_put_o,
  output logic [7:0] rx_data_o,

  // Most recent packet passes PID and CRC checks
  output logic valid_packet_o,

  // line status for the status detection (actual rx bits after clock recovery)
  output logic rx_jjj_det_o,

  // Error detection
  output logic crc_error_o,
  output logic pid_error_o,
  output logic bitstuff_error_o
);

  logic [6:0] bitstuff_history_q, bitstuff_history_d;
  logic       bitstuff_error;
  logic       bitstuff_error_q, bitstuff_error_d;

  //////////////////////
  // usb receive path //
  //////////////////////


  ///////////////////////////////////////
  // line state recovery state machine //
  ///////////////////////////////////////

  // If the receive path is set not to use a differential reciever:
  // There is a chance that one of the differential pairs will appear to have
  // changed to the new state while the other is still in the old state.  the
  // following state machine detects transitions and waits an extra sampling clock
  // before decoding the state on the differential pair.  this transition period
  // will only ever last for one clock as long as there is no noise on the line.
  // if there is enough noise on the line then the data may be corrupted and the
  // packet will fail the data integrity checks.

  // If the receive path uses a differential receiver:
  // The single ended signals must still be recovered to detect SE0
  // Note that the spec warns in section 7.1.4.1:
  // Both D+ and D- may temporarily be less than VIH (min) during differential
  // signal transitions. This period can be up to 14 ns (TFST) for full-speed
  // transitions and up to 210 ns (TLST) for low-speed transitions. Logic in the
  // receiver must ensure that that this is not interpreted as an SE0.
  // Since the 48MHz sample clock is 20.833ns period we will either miss this or
  // sample it only once, so it will be covered by line_state=DT and the next
  // sample will not be SE0 unless this was a real SE0 transition
  // Note: if it is a real SE0 the differential rx could be doing anything

  logic [2:0] line_state_qq, line_state_q, line_state_d;
  logic [2:0] diff_state_q, diff_state_d;
  logic [2:0] line_state_rx;
  logic       use_se;

  localparam logic [2:0]  DT = 3'b100; // transition state
  localparam logic [2:0]  DJ = 3'b010; // J - idle line state
  localparam logic [2:0]  DK = 3'b001; // K - inverse of J
  localparam logic [2:0] SE0 = 3'b000; // single-ended 0 - end of packet or detached
  // localparam logic [2:0] SE1 = 3'b011; // single-ended 1 - illegal

  // Mute the input if we're transmitting
  logic [1:0] dpair, ddiff;
  always_comb begin : proc_dpair_mute
    if (tx_en_i) begin
      dpair = DJ[1:0]; // J
      ddiff = DJ[1:0]; // J
    end else begin
      dpair = {usb_dp_i, usb_dn_i};
      ddiff = usb_d_i ? DJ[1:0] : DK[1:0]; // equiv to {usb_d_i, ~usb_d_i}
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_line_state_q
    if (!rst_ni) begin
      line_state_q <= SE0;
      line_state_qq <= SE0;
      diff_state_q <= SE0;
    end else begin
      if (link_reset_i) begin
        line_state_q <= SE0;
        line_state_qq <= SE0;
        diff_state_q <= SE0;
      end else begin
        line_state_q <= line_state_d;
        line_state_qq <= line_state_q;
        diff_state_q <= diff_state_d;
      end
    end
  end

  always_comb begin : proc_line_state_d
    // Default assignment
    line_state_d = line_state_q;

    if (line_state_q == DT) begin
      // if we are in a transition state, then we can sample the pair and
      // move to the next corresponding line state
      line_state_d = {1'b0, dpair};

    end else begin
      // if we are in a valid line state and the value of the pair changes,
      // then we need to move to the transition state
      if (dpair != line_state_q[1:0]) begin
        line_state_d = DT;
      end
    end
  end

  always_comb begin : proc_diff_state_d
    // Default assignment
    diff_state_d = diff_state_q;

    if (diff_state_q == DT) begin
      // if we are in a transition state, then we can sample the diff input and
      // move to the next corresponding line state
      diff_state_d = {1'b0, ddiff};

    end else begin
      // if we are in a valid line state and the value of the diff input changes,
      // then we need to move to the transition state
      if (ddiff != diff_state_q[1:0]) begin
        diff_state_d = DT;
      end
    end
  end

  // The received line state depends on how the receiver is configured:
  // Single ended only: it is just the line_state_q that was captured
  //
  // Differential: recovered from the differential receiver (diff_state_q)
  //               unless the single ended indicate SE0 when the differential
  //               receiver could produce any value
  //
  // Transition where single ended happens to see SE0 look like (driven by diff DT)
  // line_state    D? DT D?...
  // diff_state    Dx DT Dy         (expect Dy to be inverse of Dx since diff changed)
  //
  // Transition to SE0 when differential changes will look like:
  // line_state    DT D? D? D? DT SE0 SE0... (DT is the first sample at SE0)
  // diff_state    DT Dx Dx Dx DT ??  ??...  (diff saw transition as line went SE0)
  //    --> out    DT Dx Dx Dx DT SE0 SE0    (if no transition then DT would be Dx and n=3)
  // bit_phase      n  0  1  2  3  0   1     (n=3 unless there was a clock resync)
  //
  // Transition to SE0 when differential does not change will look like:
  // line_state    DT D? D? D? DT SE0 SE0... (DT is the first sample at SE0)
  // diff_state    DT Dx Dx Dx Dx ??  ??...  (diff no transition as line went SE0)
  //    --> out    DT Dx Dx Dx Dx SE0 SE0    (if no transition then DT would be Dx and n=3)
  // bit_phase      n  0  1  2  3  0   1     (n=3 unless there was a clock resync)
  //
  // Transition to SE0 when differential does not change and clock resync earlier:
  // line_state    DT D? D? DT SE0 SE0 SE0... (DT is the first sample at SE0, should resync clock)
  // diff_state    DT Dx Dx Dx Dx  ??  ??...  (diff no transition as line went SE0)
  //    --> out    DT Dx Dx Dx SE0 SE0 SE0    (if no transition then DT would be Dx and n=3)
  // bit_phase      n  0  1  2  3   0   1     (n=3 unless there was a clock resync)
  //
  // On transition back from SE0 want to generate a DT to resync the clock
  // since SE0 could have gone on a while no idea what bit_phase is
  // line_state    SE0 SE0 DT D? D? D?
  // diff_state    ??  ??  ?? Dx Dx Dx
  //   --> out     SE0 SE0 DT Dx Dx Dx
  // bit_phase      ?   ?   ?  0  1  2

  assign use_se = (line_state_q == SE0) || ((line_state_q == DT) && (line_state_qq == SE0));
  assign line_state_rx = cfg_rx_differential_i ? (use_se ? line_state_q : diff_state_q) :
                                                 line_state_q;

  ////////////////////
  // clock recovery //
  ////////////////////

  // the DT state from the line state recovery state machine is used to align to
  // transmit clock.  the line state is sampled in the middle of the bit time.

  // example of signal relationships
  // -------------------------------
  // line_state        DT  DJ  DJ  DJ  DT  DK  DK  DK  DK  DK  DK  DT  DJ  DJ  DJ
  // line_state_valid  ________----____________----____________----________----____
  // bit_phase         0   0   1   2   3   0   1   2   3   0   1   2   0   1   2


  logic [1:0] bit_phase_q, bit_phase_d;
  logic line_state_valid;

  assign line_state_valid = (bit_phase_q == 2'd1);
  assign bit_strobe_o     = (bit_phase_q == 2'd2);

  // keep track of phase within each bit
  assign bit_phase_d = (line_state_rx == DT) ? 0 : bit_phase_q + 1;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bit_phase_q
    if (!rst_ni) begin
      bit_phase_q <= 0;
    end else begin
      if (link_reset_i) begin
        bit_phase_q <= 0;
      end else begin
        bit_phase_q <= bit_phase_d;
      end
    end
  end


  //////////////////////
  // packet detection //
  //////////////////////

  // usb uses a sync to denote the beginning of a packet and two single-ended-0 to
  // denote the end of a packet.  this state machine recognizes the beginning and
  // end of packets for subsequent layers to process.

  logic [11:0] line_history_q, line_history_d;
  logic packet_valid_q, packet_valid_d;
  logic see_eop, packet_start, packet_end;

  assign packet_start = packet_valid_d & ~packet_valid_q;
  assign packet_end   = ~packet_valid_d & packet_valid_q;

  // EOP detection is configurable for 1/2 bit periods of SE0.
  // The standard (Table 7-7) mandates min = 82 ns = 1 bit period.
  // We also trigger an EOP on seeing a bitstuff error.
  assign see_eop = (cfg_eop_single_bit_i && line_history_q[1:0] == 2'b00)
    || (line_history_q[3:0] == 4'b0000) || bitstuff_error_q;

  always_comb begin : proc_packet_valid_d
    if (line_state_valid) begin
      // check for packet start: KJKJKK, we use the last 6 bits
      if (!packet_valid_q && line_history_q[11:0] == 12'b011001100101) begin
        packet_valid_d = 1;
      end

      // check for packet end: SE0 SE0
      else if (packet_valid_q && see_eop) begin
        packet_valid_d = 0;

      end else begin
        packet_valid_d = packet_valid_q;
      end
    end else begin
      packet_valid_d = packet_valid_q;
    end
  end

  // keep a history of the last two states on the line
  assign line_history_d = line_state_valid ? {line_history_q[9:0], line_state_rx[1:0]} :
                                              line_history_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_reg_pkt_line
    if (!rst_ni) begin
      packet_valid_q <= 0;
      line_history_q <= 12'b101010101010; // all K
    end else begin
      if (link_reset_i) begin
        packet_valid_q <= 0;
        line_history_q <= 12'b101010101010; // all K
      end else begin
        packet_valid_q <= packet_valid_d;
        line_history_q <= line_history_d;
      end
    end
  end

  // mask out jjj detection when transmitting (because rx is forced to J)
  assign rx_jjj_det_o = ~tx_en_i & (line_history_q[5:0] == 6'b101010); // three Js

  /////////////////
  // NRZI decode //
  /////////////////

  // in order to ensure there are enough bit transitions for a receiver to recover
  // the clock usb uses NRZI encoding.

  // https://en.wikipedia.org/wiki/Non-return-to-zero

  logic dvalid_raw;
  logic din;

  always_comb begin
    unique case (line_history_q[3:0])
      4'b0101 : din = 1;
      4'b0110 : din = 0;
      4'b1001 : din = 0;
      4'b1010 : din = 1;
      default : din = 0;
    endcase

    if (packet_valid_q && line_state_valid) begin
      unique case (line_history_q[3:0])
        4'b0101 : dvalid_raw = 1;
        4'b0110 : dvalid_raw = 1;
        4'b1001 : dvalid_raw = 1;
        4'b1010 : dvalid_raw = 1;
        default : dvalid_raw = 0;
      endcase
    end else begin
      dvalid_raw = 0;
    end
  end

  //////////////////////////////////////////////////////
  // Undo bit stuffing and detect bit stuffing errors //
  //////////////////////////////////////////////////////

  always_comb begin : proc_bitstuff_history_d
    if (packet_end) begin
      bitstuff_history_d = '0;
    end else if (dvalid_raw) begin
      bitstuff_history_d = {bitstuff_history_q[5:0], din};
    end else begin
      bitstuff_history_d = bitstuff_history_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bitstuff_history_q
    if (!rst_ni) begin
      bitstuff_history_q <= 0;
    end else begin
      if (link_reset_i) begin
        bitstuff_history_q <= 0;
      end else begin
        bitstuff_history_q <= bitstuff_history_d;
      end
    end
  end

  logic dvalid;
  assign dvalid = dvalid_raw && !(bitstuff_history_q[5:0] == 6'b111111);

  // 7 consecutive ones should not be seen on the bus
  // USB spec, 7.1.9.1: "If the receiver sees seven
  // consecutive ones anywhere in the packet, then a bit stuffing error
  // has occurred and the packet should be ignored."
  assign bitstuff_error = bitstuff_history_q == 7'b1111111;

  // remember the bitstuff errors
  always_comb begin : proc_bistuff_error_d
    bitstuff_error_d = bitstuff_error_q;
    if (packet_start) begin
      bitstuff_error_d = 0;
    end else if (bitstuff_error && dvalid_raw) begin
      bitstuff_error_d = 1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bitstuff_error_q
    if (!rst_ni) begin
      bitstuff_error_q <= 0;
    end else begin
      bitstuff_error_q <= bitstuff_error_d;
    end
  end

  assign bitstuff_error_o = bitstuff_error_q && packet_end;


  ////////////////////////
  // save and check pid //
  ////////////////////////

  // shift in the entire 8-bit pid with an additional 9th bit used as a sentinal.

  logic [8:0] full_pid_q, full_pid_d;
  logic pid_valid, pid_complete;

  assign pid_valid    = full_pid_q[4:1] == ~full_pid_q[8:5];
  assign pid_complete = full_pid_q[0];

  always_comb begin : proc_full_pid_d
    if (dvalid && !pid_complete) begin
      full_pid_d = {din, full_pid_q[8:1]};
    end else if (packet_start) begin
      full_pid_d = 9'b100000000;
    end else begin
      full_pid_d = full_pid_q;
    end
  end

  ////////////////
  // check crc5 //
  ////////////////
  logic [4:0] crc5_q, crc5_d;
  logic crc5_valid, crc5_invert;
  assign crc5_valid  = crc5_q == 5'b01100;
  assign crc5_invert = din ^ crc5_q[4];

  always_comb begin
    crc5_d = crc5_q; // default value

    if (packet_start) begin
      crc5_d = 5'b11111;
    end

    if (dvalid && pid_complete) begin
      crc5_d = {crc5_q[3:0], 1'b0} ^ ({5{crc5_invert}} & 5'b00101);
    end
  end


  /////////////////
  // check crc16 //
  /////////////////
  logic [15:0] crc16_q, crc16_d;
  logic crc16_valid, crc16_invert;

  assign crc16_valid  = crc16_q == 16'b1000000000001101;
  assign crc16_invert = din ^ crc16_q[15];

  always_comb begin
    crc16_d = crc16_q; // default value

    if (packet_start) begin
      crc16_d = 16'b1111111111111111;
    end

    if (dvalid && pid_complete) begin
      crc16_d = {crc16_q[14:0], 1'b0} ^ ({16{crc16_invert}} & 16'b1000000000000101);
    end
  end


  ////////////////////////////
  // output control signals //
  ////////////////////////////
  logic pkt_is_token, pkt_is_data, pkt_is_handshake;
  assign pkt_is_token     = full_pid_q[2:1] == 2'b01;
  assign pkt_is_data      = full_pid_q[2:1] == 2'b11;
  assign pkt_is_handshake = full_pid_q[2:1] == 2'b10;


  // TODO: need to check for data packet babble
  assign valid_packet_o = pid_valid && !bitstuff_error_q &&
    ((pkt_is_handshake) ||
    (pkt_is_data && crc16_valid) ||
    (pkt_is_token && crc5_valid)
  );

  // Detect CRC errors
  assign crc_error_o = ((pkt_is_data && !crc16_valid) ||
    (pkt_is_token && !crc5_valid)) && packet_end;

  // Detect PID errors
  assign pid_error_o = !pid_valid && packet_end;

  logic [11:0] token_payload_q, token_payload_d;
  logic token_payload_done;

  assign token_payload_done = token_payload_q[0];

  logic [6:0] addr_q, addr_d;
  logic [3:0] endp_q, endp_d;
  logic [10:0] frame_num_q, frame_num_d;

  always_comb begin
    token_payload_d = token_payload_q; // default

    if (packet_start) begin
      token_payload_d = 12'b100000000000;
    end

    if (dvalid && pid_complete && pkt_is_token && !token_payload_done) begin
      token_payload_d = {din, token_payload_q[11:1]};
    end
  end

  always_comb begin
    // defaults
    addr_d      = addr_q;
    endp_d      = endp_q;
    frame_num_d = frame_num_q;

    if (token_payload_done && pkt_is_token) begin
      addr_d      = token_payload_q[7:1];
      endp_d      = token_payload_q[11:8];
      frame_num_d = token_payload_q[11:1];
    end
  end

  assign addr_o      = addr_q;
  assign endp_o      = endp_q;
  assign frame_num_o = frame_num_q;
  assign pid_o       = full_pid_q[4:1];

  assign pkt_start_o = packet_start;
  assign pkt_end_o   = packet_end;


  /////////////////////////////////
  // deserialize and output data //
  /////////////////////////////////
  //assign rx_data_put = dvalid && pid_complete && pkt_is_data;
  logic [8:0] rx_data_buffer_q, rx_data_buffer_d;
  logic rx_data_buffer_full;

  assign rx_data_buffer_full = rx_data_buffer_q[0];
  assign rx_data_put_o       = rx_data_buffer_full;
  assign rx_data_o           = rx_data_buffer_q[8:1];

  always_comb begin
    rx_data_buffer_d = rx_data_buffer_q; // default

    if (packet_start || rx_data_buffer_full) begin
      rx_data_buffer_d = 9'b100000000;
    end

    if (dvalid && pid_complete && pkt_is_data) begin
      rx_data_buffer_d = {din, rx_data_buffer_q[8:1]};
    end
  end


  ///////////////
  // Registers //
  ///////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_gp_regs
    if (!rst_ni) begin
      full_pid_q          <= 0;
      crc16_q             <= 0;
      crc5_q              <= 0;
      token_payload_q     <= 0;
      addr_q              <= 0;
      endp_q              <= 0;
      frame_num_q         <= 0;
      rx_data_buffer_q    <= 0;
    end else begin
      if (link_reset_i) begin
        full_pid_q          <= 0;
        crc16_q             <= 0;
        crc5_q              <= 0;
        token_payload_q     <= 0;
        addr_q              <= 0;
        endp_q              <= 0;
        frame_num_q         <= 0;
        rx_data_buffer_q    <= 0;
      end else begin
        full_pid_q          <= full_pid_d;
        crc16_q             <= crc16_d;
        crc5_q              <= crc5_d;
        token_payload_q     <= token_payload_d;
        addr_q              <= addr_d;
        endp_q              <= endp_d;
        frame_num_q         <= frame_num_d;
        rx_data_buffer_q    <= rx_data_buffer_d;
      end
    end
  end

endmodule // usb_fs_rx
