// Copyright lowRISC contributors.
// Copyright ETH Zurich.
// Copyright Luke Valenty (TinyFPGA project, https://github.com/tinyfpga/TinyFPGA-Bootloader).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module usb_fs_tx (
  // A 48MHz clock is required to receive USB data at 12MHz
  // it's simpler to juse use 48MHz everywhere
  input  logic clk_i,
  input  logic rst_ni,  // asyc reset
  input  logic link_reset_i, // USB reset, sync to 48 MHz, active high

  // bit strobe from rx to align with senders clock
  input  logic bit_strobe_i,

  // output enable to take ownership of bus and data out
  output logic oe_o,
  output logic dp_o,
  output logic dn_o,

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


  typedef enum {IDLE, SYNC, PID, DATA_OR_CRC16_0, CRC16_1, EOP} state_t;

    
  // -------------------------------------------------
  //  Signal Declarations
  // -------------------------------------------------
  logic [3:0] pid_q, pid_d;
  logic bitstuff;
  logic bitstuff_q;
  logic bitstuff_qq;
  logic bitstuff_qqq;
  logic bitstuff_qqqq;

  logic [5:0] bit_history;

  state_t state_d, state_q;


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
  logic dp_q, dp_d;
  logic dn_q, dn_d;
  logic [2:0] dp_eop_q, dp_eop_d;

  logic serial_tx_data;
  logic serial_tx_oe;
  logic serial_tx_se0;
  logic crc16_invert;

  // save packet parameters at pkt_start_i
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_pid
    if(!rst_ni) begin
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
  assign bitstuff = bit_history == 6'b111111;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_bitstuff
    if(!rst_ni) begin
      bitstuff_q <= 0;
      bitstuff_qq <= 0;
      bitstuff_qqq <= 0;
      bitstuff_qqqq <= 0;
    end else begin
      if (link_reset_i) begin
        bitstuff_q <= 0;
        bitstuff_qq <= 0;
        bitstuff_qqq <= 0;
        bitstuff_qqqq <= 0;          
      end else begin
        bitstuff_q <= bitstuff;
        bitstuff_qq <= bitstuff_q;
        bitstuff_qqq <= bitstuff_qq;
        bitstuff_qqqq <= bitstuff_qqq;
      end
    end
  end

  assign pkt_end_o = bit_strobe_i && se0_shift_reg_q[1:0] == 2'b01;


  // -------------------------------------------------
  //  FSM
  // -------------------------------------------------
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


    case (state_q)
      IDLE : begin
        if (pkt_start_i) begin
          state_d = SYNC;
        end
      end

      SYNC : begin
        if (byte_strobe_q) begin
          state_d = PID;
          data_shift_reg_d = 8'b10000000;
          oe_shift_reg_d = 8'b11111111;
          se0_shift_reg_d = 8'b00000000;
        end
      end

      PID : begin
        if (byte_strobe_q) begin
          if (pid_q[1:0] == 2'b11) begin
            state_d = DATA_OR_CRC16_0;
          end else begin
            state_d = EOP;
          end

          data_shift_reg_d = {~pid_q, pid_q};
          oe_shift_reg_d = 8'b11111111;
          se0_shift_reg_d = 8'b00000000;
        end
      end

      DATA_OR_CRC16_0 : begin
        if (byte_strobe_q) begin
          if (tx_data_avail_i) begin
            state_d = DATA_OR_CRC16_0;
            data_payload_d = 1;
            tx_data_get_d = 1;
            data_shift_reg_d = tx_data_i;
            oe_shift_reg_d = 8'b11111111;
            se0_shift_reg_d = 8'b00000000;
          end else begin
            state_d = CRC16_1;
            data_payload_d = 0;
            tx_data_get_d = 0;
            data_shift_reg_d = ~{crc16_q[8], crc16_q[9], crc16_q[10], crc16_q[11], crc16_q[12], crc16_q[13], crc16_q[14], crc16_q[15]};
            oe_shift_reg_d = 8'b11111111;
            se0_shift_reg_d = 8'b00000000;
          end
        end else begin
          tx_data_get_d = 0; 
        end
      end

      CRC16_1 : begin
        if (byte_strobe_q) begin
          state_d = EOP;
          data_shift_reg_d = ~{crc16_q[0], crc16_q[1], crc16_q[2], crc16_q[3], crc16_q[4], crc16_q[5], crc16_q[6], crc16_q[7]};
          oe_shift_reg_d = 8'b11111111;
          se0_shift_reg_d = 8'b00000000;
        end
      end

      EOP : begin
        if (byte_strobe_q) begin
          state_d = IDLE;
          oe_shift_reg_d = 8'b00000111;
          se0_shift_reg_d = 8'b00000111;
        end
      end
    endcase

    // Logic closely coupled to the FSM
    if (pkt_start_i) begin
      bit_count_d   = 1;
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

  always_comb begin : proc_byte_str
    if (bit_strobe_i && !bitstuff) begin
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

    if (bit_strobe_i && data_payload_q && !bitstuff_qqqq && !pkt_start_i) begin
      crc16_d[15] = crc16_q[14] ^ crc16_invert;
      crc16_d[14] = crc16_q[13];
      crc16_d[13] = crc16_q[12];
      crc16_d[12] = crc16_q[11];
      crc16_d[11] = crc16_q[10];
      crc16_d[10] = crc16_q[9];
      crc16_d[9] = crc16_q[8];
      crc16_d[8] = crc16_q[7];
      crc16_d[7] = crc16_q[6];
      crc16_d[6] = crc16_q[5];
      crc16_d[5] = crc16_q[4];
      crc16_d[4] = crc16_q[3];
      crc16_d[3] = crc16_q[2];
      crc16_d[2] = crc16_q[1] ^ crc16_invert;
      crc16_d[1] = crc16_q[0];
      crc16_d[0] = crc16_invert;
    end      
  end

  // -------------------------------------------------
  //  Regular Registers
  // -------------------------------------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_reg
    if(!rst_ni) begin
      state_q           <= IDLE;
      data_payload_q    <= 0;
      data_shift_reg_q  <= 0;
      oe_shift_reg_q    <= 0;
      se0_shift_reg_q   <= 0;
      data_payload_q    <= 0;
      tx_data_get_q     <= 0;
      byte_strobe_q     <= 0;
      bit_history_q     <= 0;
      bit_count_q       <= 0;
      crc16_q           <= 0;
    end else begin
      if (link_reset_i) begin
        state_q           <= IDLE;
        data_payload_q    <= 0;
        data_shift_reg_q  <= 0;
        oe_shift_reg_q    <= 0;
        se0_shift_reg_q   <= 0;
        data_payload_q    <= 0;
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
        data_payload_q    <= data_payload_d;
        tx_data_get_q     <= tx_data_get_d;
        byte_strobe_q     <= byte_strobe_d;
        bit_history_q     <= bit_history_d;
        bit_count_q       <= bit_count_d;
        crc16_q           <= crc16_d;
      end
    end
  end

  // -------------------------------------------------
  // nrzi and differential driving
  // -------------------------------------------------
  always_comb begin : proc_diff
    dp_d     = dp_q;
    dn_d     = dn_q;
    oe_d     = oe_q;
    dp_eop_d = dp_eop_q;

    if (pkt_start_i) begin
      // J
      dp_d = 1;
      dn_d = 0;
      
      dp_eop_d = 3'b100;

    end else if (bit_strobe_i) begin
      oe_d = serial_tx_oe;

      if (serial_tx_se0) begin
        dp_d = dp_eop_q[0];
        dn_d = 0;

        dp_eop_d = dp_eop_q >> 1;

      end else if (serial_tx_data) begin
        // value should stay the same, do nothing

      end else begin
        dp_d = !dp_q;
        dn_d = !dn_q;
      end
    end
  
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_diff_reg
    if(!rst_ni) begin
      dp_eop_q  <= 0;
      oe_q      <= 0;
      dp_q      <= 0;
      dn_q      <= 0;
    end else begin
      if (link_reset_i) begin
        dp_eop_q  <= 0;
        oe_q      <= 0;
        dp_q      <= 0;
        dn_q      <= 0;        
      end else begin
        dp_eop_q  <= dp_eop_d;
        oe_q      <= oe_d;
        dp_q      <= dp_d;
        dn_q      <= dn_d;
      end
    end
  end

  assign oe_o = oe_q;
  assign dp_o = dp_q;
  assign dn_o = dn_q;

endmodule
