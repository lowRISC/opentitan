// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Copyright Luke Valenty (TinyFPGA project, https://github.com/tinyfpga/TinyFPGA-Bootloader).

module usb_fs_tx (
  // A 48MHz clock is required to receive USB data at 12MHz
  // it's simpler to juse use 48MHz everywhere
  input  logic clk_i,
  input  logic rst_ni,  // asyc reset
  input  logic link_reset_i, // USB reset, sync to 48 MHz, active high
  input  logic cfg_pinflip_i,

  // Oscillator test mode (constantly output JK)
  input  logic tx_osc_test_mode_i,

  // bit strobe from rx to align with senders clock
  input  logic bit_strobe_i,

  // output enable to take ownership of bus and data out
  output logic usb_oe_o,
  output logic usb_d_o,
  output logic usb_se0_o,
  output logic usb_dp_o,
  output logic usb_dn_o,

  // pulse to initiate new packet transmission
  input  logic pkt_start_i,
  output logic pkt_end_o,

  // pid_i to send
  input  logic [3:0] pid_i,

  // tx logic pulls data until there is nothing available
  input  logic tx_data_avail_i,
  output logic tx_data_get_o,
  input  logic [7:0] tx_data_i
);


  typedef enum logic [2:0] {Idle, Sync, Pid, DataOrCrc160, Crc161, Eop, OscTest} state_e;
  typedef enum logic [1:0] {OsIdle, OsWaitByte, OsTransmit} out_state_e;


  /////////////////////////
  // Signal Declarations //
  /////////////////////////
  logic [3:0] pid_q, pid_d;
  logic bitstuff;
  logic bitstuff_q;
  logic bitstuff_q2;
  logic bitstuff_q3;
  logic bitstuff_q4;

  logic [5:0] bit_history;

  state_e      state_d, state_q;
  out_state_e  out_state_d, out_state_q;


  logic [7:0] data_shift_reg_q, data_shift_reg_d;
  logic [7:0] oe_shift_reg_q, oe_shift_reg_d;
  logic [7:0] se0_shift_reg_q, se0_shift_reg_d;
  logic data_payload_q, data_payload_d;
  logic tx_data_get_q, tx_data_get_d;
  logic byte_strobe_q, byte_strobe_d;
  logic [4:0] bit_history_d, bit_history_q;
  logic [2:0] bit_count_d, bit_count_q;

  logic [15:0] crc16_d, crc16_q;

  logic oe_q, oe_d;
  logic usb_d_q, usb_d_d;
  logic usb_se0_q, usb_se0_d;
  logic [2:0] dp_eop_q, dp_eop_d;

  logic test_mode_start;
  logic serial_tx_data;
  logic serial_tx_oe;
  logic serial_tx_se0;
  logic crc16_invert;
  logic pkt_end;
  logic out_nrzi_en;

  // save packet parameters at pkt_start_i
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_pid
    if (!rst_ni) begin
      pid_q <= 0;
    end else begin
      if (link_reset_i) begin
        pid_q <= 0;
      end else begin
        pid_q <= pid_d;
      end
    end
  end

  assign pid_d = pkt_start_i ? pid_i : pid_q;


  assign serial_tx_data = data_shift_reg_q[0];
  assign serial_tx_oe = oe_shift_reg_q[0];
  assign serial_tx_se0 = se0_shift_reg_q[0];


  // serialize sync, pid_i, data payload, and crc16
  assign bit_history = {serial_tx_data, bit_history_q};
  assign bitstuff    = bit_history == 6'b111111;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bitstuff
    if (!rst_ni) begin
      bitstuff_q  <= 0;
      bitstuff_q2 <= 0;
      bitstuff_q3 <= 0;
      bitstuff_q4 <= 0;
    end else begin
      if (link_reset_i) begin
        bitstuff_q  <= 0;
        bitstuff_q2 <= 0;
        bitstuff_q3 <= 0;
        bitstuff_q4 <= 0;
      end else begin
        bitstuff_q  <= bitstuff;
        bitstuff_q2 <= bitstuff_q;
        bitstuff_q3 <= bitstuff_q2;
        bitstuff_q4 <= bitstuff_q3;
      end
    end
  end

  assign pkt_end   = bit_strobe_i && se0_shift_reg_q[1:0] == 2'b01;
  assign pkt_end_o = pkt_end;


  /////////
  // FSM //
  /////////
  always_comb begin : proc_fsm
    // Default assignments
    state_d          = state_q;
    data_shift_reg_d = data_shift_reg_q;
    oe_shift_reg_d   = oe_shift_reg_q;
    se0_shift_reg_d  = se0_shift_reg_q;
    data_payload_d   = data_payload_q;
    tx_data_get_d    = tx_data_get_q;
    bit_history_d    = bit_history_q;
    bit_count_d      = bit_count_q;
    test_mode_start  = 0;

    unique case (state_q)
      Idle : begin
        if (tx_osc_test_mode_i) begin
          state_d         = OscTest;
          test_mode_start = 1;
        end else if (pkt_start_i) begin
          state_d = Sync;
        end
      end

      Sync : begin
        if (byte_strobe_q) begin
          state_d = Pid;
          data_shift_reg_d = 8'b10000000;
          oe_shift_reg_d = 8'b11111111;
          se0_shift_reg_d = 8'b00000000;
        end
      end

      Pid : begin
        if (byte_strobe_q) begin
          if (pid_q[1:0] == 2'b11) begin
            state_d = DataOrCrc160;
          end else begin
            state_d = Eop;
          end

          data_shift_reg_d = {~pid_q, pid_q};
          oe_shift_reg_d = 8'b11111111;
          se0_shift_reg_d = 8'b00000000;
        end
      end

      DataOrCrc160 : begin
        if (byte_strobe_q) begin
          if (tx_data_avail_i) begin
            state_d = DataOrCrc160;
            data_payload_d = 1;
            tx_data_get_d = 1;
            data_shift_reg_d = tx_data_i;
            oe_shift_reg_d = 8'b11111111;
            se0_shift_reg_d = 8'b00000000;
          end else begin
            state_d = Crc161;
            data_payload_d = 0;
            tx_data_get_d = 0;
            data_shift_reg_d = ~{crc16_q[8],  crc16_q[9],  crc16_q[10], crc16_q[11],
                                 crc16_q[12], crc16_q[13], crc16_q[14], crc16_q[15]};
            oe_shift_reg_d = 8'b11111111;
            se0_shift_reg_d = 8'b00000000;
          end
        end else begin
          tx_data_get_d = 0;
        end
      end

      Crc161 : begin
        if (byte_strobe_q) begin
          state_d = Eop;
          data_shift_reg_d = ~{crc16_q[0], crc16_q[1], crc16_q[2], crc16_q[3],
                               crc16_q[4], crc16_q[5], crc16_q[6], crc16_q[7]};
          oe_shift_reg_d = 8'b11111111;
          se0_shift_reg_d = 8'b00000000;
        end
      end

      Eop : begin
        if (byte_strobe_q) begin
          state_d = Idle;
          oe_shift_reg_d = 8'b00000111;
          se0_shift_reg_d = 8'b00000111;
        end
      end

      OscTest: begin
        // Oscillator test mode: toggle constantly
        if (!tx_osc_test_mode_i && byte_strobe_q) begin
          oe_shift_reg_d   = 8'b00000000;
          state_d = Idle;
        end else if (byte_strobe_q) begin
          data_shift_reg_d = 8'b00000000;
          oe_shift_reg_d   = 8'b11111111;
          se0_shift_reg_d  = 8'b00000000;
        end
      end

      default: state_d = Idle;
    endcase

    // Logic closely coupled to the FSM
    if (pkt_start_i) begin
      // We need to have an inter-packet delay between
      // 2 and 6.5 bit times (see USB 2.0 spec / 7.1.18.1)
      // The latency in the rest of the system is approximately (measured)
      // 3.68 bit-times, so we only introduce 1 bit-time here
      bit_count_d   = 7; // 8-7 = 1
      bit_history_d = 0;

    end else if (bit_strobe_i) begin
      // bitstuff
      if (bitstuff /* && !serial_tx_se0*/) begin
        bit_history_d       = bit_history[5:1];
        data_shift_reg_d[0] = 0;

      // normal deserialize
      end else begin
        bit_count_d = bit_count_q + 1;

        data_shift_reg_d  = (data_shift_reg_q >> 1);
        oe_shift_reg_d    = (oe_shift_reg_q >> 1);
        se0_shift_reg_d   = (se0_shift_reg_q >> 1);

        bit_history_d = bit_history[5:1];
      end
    end
  end

  `ASSERT(StateValid_A, state_q inside {Idle, Sync, Pid, DataOrCrc160, Crc161, Eop, OscTest})

  always_comb begin : proc_byte_str
    if (bit_strobe_i && !bitstuff && !pkt_start_i) begin
      byte_strobe_d = (bit_count_q == 3'b000);
    end else begin
      byte_strobe_d = 0;
    end

  end

  assign tx_data_get_o = tx_data_get_q;

  // calculate crc16
  assign crc16_invert = serial_tx_data ^ crc16_q[15];

  always_comb begin : proc_crc16
    crc16_d = crc16_q; // default assignment

    if (pkt_start_i) begin
      crc16_d = 16'b1111111111111111;
    end

    if (bit_strobe_i && data_payload_q && !bitstuff_q4 && !pkt_start_i) begin
      crc16_d = {crc16_q[14:0], 1'b0} ^ ({16{crc16_invert}} & 16'b1000000000000101);
    end
  end

  ///////////////////////
  // Regular Registers //
  ///////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_reg
    if (!rst_ni) begin
      state_q           <= Idle;
      data_payload_q    <= 0;
      data_shift_reg_q  <= 0;
      oe_shift_reg_q    <= 0;
      se0_shift_reg_q   <= 0;
      tx_data_get_q     <= 0;
      byte_strobe_q     <= 0;
      bit_history_q     <= 0;
      bit_count_q       <= 0;
      crc16_q           <= 0;
    end else begin
      if (link_reset_i) begin
        state_q           <= Idle;
        data_payload_q    <= 0;
        data_shift_reg_q  <= 0;
        oe_shift_reg_q    <= 0;
        se0_shift_reg_q   <= 0;
        tx_data_get_q     <= 0;
        byte_strobe_q     <= 0;
        bit_history_q     <= 0;
        bit_count_q       <= 0;
        crc16_q           <= 0;
      end else begin
        state_q           <= state_d;
        data_payload_q    <= data_payload_d;
        data_shift_reg_q  <= data_shift_reg_d;
        oe_shift_reg_q    <= oe_shift_reg_d;
        se0_shift_reg_q   <= se0_shift_reg_d;
        tx_data_get_q     <= tx_data_get_d;
        byte_strobe_q     <= byte_strobe_d;
        bit_history_q     <= bit_history_d;
        bit_count_q       <= bit_count_d;
        crc16_q           <= crc16_d;
      end
    end
  end

  ///////////////////////////////////
  // nrzi and differential driving //
  ///////////////////////////////////

  // Output FSM
  always_comb begin : proc_out_fsm
    out_state_d          = out_state_q;
    out_nrzi_en          = 1'b0;

    unique case (out_state_q)
      OsIdle: begin
        if (pkt_start_i || test_mode_start) begin
          out_state_d = OsWaitByte;
        end
      end

      OsWaitByte: begin
        if (byte_strobe_q) begin
          out_state_d = OsTransmit;
        end
      end

      OsTransmit: begin
        out_nrzi_en          = 1'b1;
        if ((bit_strobe_i && !serial_tx_oe)) begin
          out_state_d = OsIdle;
        end
      end

      default : out_state_d = OsIdle;
    endcase
  end

  `ASSERT(OutStateValid_A, out_state_q inside {OsIdle, OsWaitByte, OsTransmit})

  always_comb begin : proc_diff
    usb_d_d   = usb_d_q;
    usb_se0_d = usb_se0_q;
    oe_d     = oe_q;
    dp_eop_d = dp_eop_q;

    if (pkt_start_i) begin
      usb_d_d = 1; // J -> first bit will be K (start of sync)
      dp_eop_d = 3'b100; // Eop: {SE0, SE0, J}

    end else if (bit_strobe_i && out_nrzi_en) begin
      oe_d = serial_tx_oe;

      if (serial_tx_se0) begin
        // Eop
        dp_eop_d = dp_eop_q >> 1;

        if (dp_eop_q[0]) begin
          // last bit of Eop: J
          usb_d_d   = 1;
          usb_se0_d = 0;
        end else begin
          // first two bits of Eop: SE0
          usb_se0_d = 1;
        end

      end else if (serial_tx_data) begin
        // value should stay the same, do nothing

      end else begin
        usb_d_d = !usb_d_q;
      end

      // Set to J state when OE=0 to avoid
      // glitches
      if (!oe_d) begin
        usb_d_d = 1;
      end
    end

  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_diff_reg
    if (!rst_ni) begin
      dp_eop_q             <= 0;
      out_state_q          <= OsIdle;
    end else begin
      if (link_reset_i) begin
        dp_eop_q             <= 0;
        out_state_q          <= OsIdle;
      end else begin
        dp_eop_q             <= dp_eop_d;
        out_state_q          <= out_state_d;
      end
    end
  end


  prim_flop u_oe_flop (
    .clk_i,
    .rst_ni,
    .d_i(link_reset_i ? 1'b0 : oe_d),
    .q_o(oe_q)
  );

  prim_flop #(
    .ResetValue(1) // J state = idle state
  ) u_usb_d_flop (
    .clk_i,
    .rst_ni,
    .d_i(link_reset_i ? 1'b0 : usb_d_d),
    .q_o(usb_d_q)
  );

  prim_flop u_usb_se0_flop (
    .clk_i,
    .rst_ni,
    .d_i(link_reset_i ? 1'b0 : usb_se0_d),
    .q_o(usb_se0_q)
  );

  // Handle the D+ / D- pin flip on the USB side, and provide both the
  // dp/dn and d/se0 interfaces, for compatibility with multiple driver types.
  logic usb_se0_flipped, usb_dp_flipped, usb_dn_flipped;

  always_comb begin
    if (link_reset_i) begin
      usb_se0_flipped = 1'b0;
      usb_dp_flipped = 1'b0 ^ cfg_pinflip_i;
      usb_dn_flipped = 1'b1 ^ cfg_pinflip_i;
    end else begin
      usb_se0_flipped = usb_se0_d;
      usb_dp_flipped = (cfg_pinflip_i ? ~usb_d_d :  usb_d_d) & ~usb_se0_d;
      usb_dn_flipped = (cfg_pinflip_i ?  usb_d_d : ~usb_d_d) & ~usb_se0_d;
    end
  end

  // Use registered outputs for the I/Os
  prim_flop #(
    .ResetValue(1) // J state = idle state
  ) u_usb_d_o_flop (
    .clk_i,
    .rst_ni,
    .d_i(usb_dp_flipped),  // Note: single-ended 'D' output mirrors D+
    .q_o(usb_d_o)
  );

  prim_flop #(
    .ResetValue(0) // J state = idle state
  ) u_usb_se0_o_flop (
    .clk_i,
    .rst_ni,
    .d_i(usb_se0_flipped),
    .q_o(usb_se0_o)
  );

  prim_flop #(
    .ResetValue(1) // J state = idle state
  ) u_usb_dp_o_flop (
    .clk_i,
    .rst_ni,
    .d_i(usb_dp_flipped),
    .q_o(usb_dp_o)
  );

  prim_flop #(
    .ResetValue(0) // J state = idle state
  ) u_usb_dn_o_flop (
    .clk_i,
    .rst_ni,
    .d_i(usb_dn_flipped),
    .q_o(usb_dn_o)
  );

  assign usb_oe_o  = oe_q;

endmodule
