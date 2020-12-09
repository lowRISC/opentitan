// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C finite state machine

module i2c_fsm (
  input        clk_i,  // clock
  input        rst_ni, // active low reset

  input        scl_i,  // serial clock input from i2c bus
  output       scl_o,  // serial clock output to i2c bus
  input        sda_i,  // serial data input from i2c bus
  output       sda_o,  // serial data output to i2c bus

  input        host_enable_i, // enable host functionality
  input        target_enable_i, // enable target functionality

  input        fmt_fifo_rvalid_i, // indicates there is valid data in fmt_fifo
  input        fmt_fifo_wvalid_i, // indicates data is being put into fmt_fifo
  input [5:0]  fmt_fifo_depth_i,  // fmt_fifo_depth
  output logic fmt_fifo_rready_o, // populates fmt_fifo
  input [7:0]  fmt_byte_i,        // byte in fmt_fifo to be sent to target
  input        fmt_flag_start_before_i, // issue start before sending byte
  input        fmt_flag_stop_after_i,   // issue stop after sending byte
  input        fmt_flag_read_bytes_i,   // indicates byte is an number of reads
  input        fmt_flag_read_continue_i,// host to send Ack to final byte read
  input        fmt_flag_nak_ok_i,       // no Ack is expected

  output logic       rx_fifo_wvalid_o, // high if there is valid data in rx_fifo
  output logic [7:0] rx_fifo_wdata_o,  // byte in rx_fifo read from target

  input        tx_fifo_rvalid_i, // indicates there is valid data in tx_fifo
  input        tx_fifo_wvalid_i, // indicates data is being put into tx_fifo
  input [5:0]  tx_fifo_depth_i,  // tx_fifo_depth
  output logic tx_fifo_rready_o, // populates tx_fifo
  input [7:0]  tx_fifo_rdata_i,  // byte in tx_fifo to be sent to host

  output logic       acq_fifo_wvalid_o, // high if there is valid data in acq_fifo
  output logic [9:0] acq_fifo_wdata_o,  // byte and signal in acq_fifo read from target

  output logic       host_idle_o,      // indicates the host is idle
  output logic       target_idle_o,    // indicates the target is idle

  input [15:0] thigh_i,    // high period of the SCL in clock units
  input [15:0] tlow_i,     // low period of the SCL in clock units
  input [15:0] t_r_i,      // rise time of both SDA and SCL in clock units
  input [15:0] t_f_i,      // fall time of both SDA and SCL in clock units
  input [15:0] thd_sta_i,  // hold time for (repeated) START in clock units
  input [15:0] tsu_sta_i,  // setup time for repeated START in clock units
  input [15:0] tsu_sto_i,  // setup time for STOP in clock units
  input [15:0] tsu_dat_i,  // data setup time in clock units
  input [15:0] thd_dat_i,  // data hold time in clock units
  input [15:0] t_buf_i,    // bus free time between STOP and START in clock units
  input [30:0] stretch_timeout_i,  // max time target may stretch the clock
  input        timeout_enable_i,   // assert if target stretches clock past max

  input logic [6:0] target_address0_i,
  input logic [6:0] target_mask0_i,
  input logic [6:0] target_address1_i,
  input logic [6:0] target_mask1_i,

  output logic event_nak_o,              // target didn't Ack when expected
  output logic event_scl_interference_o, // other device forcing SCL low
  output logic event_sda_interference_o, // other device forcing SDA low
  output logic event_stretch_timeout_o,  // target stretches clock past max time
  output logic event_sda_unstable_o,     // SDA is not constant during SCL pulse
  output logic event_trans_complete_o,   // Transaction is complete
  output logic event_tx_empty_o,         // tx_fifo is empty but data is needed
  output logic event_tx_nonempty_o,      // tx_fifo is nonempty after stop
  output logic event_ack_stop_o          // target received stop after ack
);

  // I2C bus clock timing variables
  logic [19:0] tcount_q;      // current counter for setting delays
  logic [19:0] tcount_d;      // next counter for setting delays
  logic        load_tcount;   // indicates counter must be loaded
  logic [30:0] stretch;       // counter for clock being stretched by target

  // Bit and byte counter variables
  logic [2:0]  bit_index;     // bit being transmitted to or read from the bus
  logic        bit_decr;      // indicates bit_index must be decremented by 1
  logic        bit_clr;       // indicates bit_index must be reset to 7
  logic [8:0]  byte_num;      // number of bytes to read
  logic [8:0]  byte_index;    // byte being read from the bus
  logic        byte_decr;     // indicates byte_index must be decremented by 1
  logic        byte_clr;      // indicates byte_index must be reset to byte_num

  // Other internal variables
  logic        scl_temp;      // scl internal
  logic        sda_temp;      // data internal
  logic        scl_i_q;       // scl_i delayed by one clock
  logic        sda_i_q;       // sda_i delayed by one clock
  logic [7:0]  read_byte;     // register for reads from target
  logic        read_byte_clr; // clear read_byte contents
  logic        shift_data_en; // indicates data must be shifted in from the bus
  logic        no_stop;       // indicates no stop has been issued before start
  logic        log_start;     // indicates start is been issued
  logic        log_stop;      // indicates stop is been issued
  logic        restart;       // indicates repeated start state is entered into

  // Target specific variables
  logic        start_det;     // indicates start or repeated start is detected on the bus
  logic        stop_det;      // indicates stop is detected on the bus
  logic        address0_match;// indicates target's address0 matches the one sent by host
  logic        address1_match;// indicates target's address1 matches the one sent by host
  logic        address_match; // indicates one of target's addresses matches the one sent by host
  logic [7:0]  input_byte;    // register for reads from host
  logic        input_byte_clr;// clear input_byte contents

  // Target bit counter variables
  logic [3:0]  bit_idx;       // bit index including ack/nack
  logic        bit_ack;       // indicates ACK bit been sent or received
  logic        rw_bit;        // indicates host wants to read (1) or write (0)
  logic        host_ack;      // indicates host acqnowledged transmitted byte

  // Clock counter implementation
  typedef enum logic [3:0] {
    tSetupStart, tHoldStart, tClockLow, tSetupBit, tClockPulse, tHoldBit,
        tClockStart, tClockStop, tSetupStop, tHoldStop, tNoDelay
  } tcount_sel_e;

  tcount_sel_e tcount_sel;

  always_comb begin : counter_functions
    tcount_d = tcount_q;
    if (load_tcount) begin
      unique case (tcount_sel)
        tSetupStart : tcount_d = 20'(t_r_i) + 20'(tsu_sta_i);
        tHoldStart  : tcount_d = 20'(t_f_i) + 20'(thd_sta_i);
        tClockStart : tcount_d = 20'(thd_dat_i);
        tClockLow   : tcount_d = 20'(tlow_i) - 20'(t_r_i) - 20'(tsu_dat_i) - 20'(thd_dat_i);
        tSetupBit   : tcount_d = 20'(t_r_i) + 20'(tsu_dat_i);
        tClockPulse : tcount_d = 20'(t_r_i) + 20'(thigh_i) + 20'(t_f_i);
        tHoldBit    : tcount_d = 20'(t_f_i) + 20'(thd_dat_i);
        tClockStop  : tcount_d = 20'(t_f_i) + 20'(tlow_i) - 20'(thd_dat_i);
        tSetupStop  : tcount_d = 20'(t_r_i) + 20'(tsu_sto_i);
        tHoldStop   : tcount_d = 20'(t_r_i) + 20'(t_buf_i) - 20'(tsu_sta_i);
        tNoDelay    : tcount_d = 20'h00001;
        default     : tcount_d = 20'h00001;
      endcase
    end else if (stretch == '0) begin
      tcount_d = tcount_q - 1'b1;
    end else begin
      tcount_d = tcount_q;  // pause timer if clock is stretched
    end
  end

  always_ff @ (posedge clk_i or negedge rst_ni) begin : clk_counter
    if (!rst_ni) begin
      tcount_q <= '1;
    end else begin
      tcount_q <= tcount_d;
    end
  end

  // Clock stretching detection
  always_ff @ (posedge clk_i or negedge rst_ni) begin : clk_stretch
    if (!rst_ni) begin
      stretch <= '0;
    end else if (scl_temp == 1'b1 && scl_i == '0) begin
      stretch <= stretch + 1'b1;
    end else begin
      stretch <= '0;
    end
  end

  // Bit index implementation
  always_ff @ (posedge clk_i or negedge rst_ni) begin : bit_counter
    if (!rst_ni) begin
      bit_index <= 3'd7;
    end else if (bit_clr) begin
      bit_index <= 3'd7;
    end else if (bit_decr) begin
      bit_index <= bit_index - 1'b1;
    end else begin
      bit_index <= bit_index;
    end
  end

  // Deserializer for a byte read from the bus
  always_ff @ (posedge clk_i or negedge rst_ni) begin : read_register
    if (!rst_ni) begin
      read_byte <= 8'h00;
    end else if (read_byte_clr) begin
      read_byte <= 8'h00;
    end else if (shift_data_en) begin
      read_byte[7:0] <= {read_byte[6:0], sda_i};  // MSB goes in first
    end
  end

  // Number of bytes to read
  always_comb begin : byte_number
    if (!fmt_flag_read_bytes_i) byte_num = 9'd0;
    else if (fmt_byte_i == '0) byte_num = 9'd256;
    else byte_num = 9'(fmt_byte_i);
  end

  // Byte index implementation
  always_ff @ (posedge clk_i or negedge rst_ni) begin : byte_counter
    if (!rst_ni) begin
      byte_index <= '0;
    end else if (byte_clr) begin
      byte_index <= byte_num;
    end else if (byte_decr) begin
      byte_index <= byte_index - 1'b1;
    end else begin
      byte_index <= byte_index;
    end
  end

  // SDA and SCL at the previous clock edge
  always_ff @ (posedge clk_i or negedge rst_ni) begin : bus_prev
    if (!rst_ni) begin
      scl_i_q <= 1'b1;
      sda_i_q <= 1'b1;
    end else begin
      scl_i_q <= scl_i;
      sda_i_q <= sda_i;
    end
  end

  // Stop issued before
  always_ff @ (posedge clk_i or negedge rst_ni) begin : stop_state
    if (!rst_ni) begin
      no_stop <= 1'b0;
    end else if (log_stop) begin
      no_stop <= 1'b0;
    end else if (log_start) begin
      no_stop <= 1'b1;
    end else begin
      no_stop <= no_stop;
    end
  end

  // (Repeated) Start condition detection by target
  always_ff @ (posedge clk_i or negedge rst_ni) begin : s_detect
    if (!rst_ni) begin
      start_det <= 1'b0;
    end else if (scl_i_q == 1'b1 && scl_i == 1'b1) begin
      if (sda_i_q == 1'b1 && sda_i == '0) start_det <= 1'b1;
      else start_det <= 1'b0;
    end else begin
      start_det <= 1'b0;
    end
  end

  // Stop condition detection by target
  always_ff @ (posedge clk_i or negedge rst_ni) begin : p_detect
    if (!rst_ni) begin
      stop_det <= 1'b0;
    end else if (scl_i_q == 1'b1 && scl_i == 1'b1) begin
      if (sda_i_q == '0 && sda_i == 1'b1) stop_det <= 1'b1;
      else stop_det <= 1'b0;
    end else begin
      stop_det <= 1'b0;
    end
  end

  // Bit counter on the target side
  assign bit_ack = (bit_idx == 4'd8) && !start_det; // ack

  // Increment counter on negative SCL edge
  always_ff @ (posedge clk_i or negedge rst_ni) begin : tgt_bit_counter
    if (!rst_ni) begin
      bit_idx <= 4'd0;
    end else if (start_det || bit_ack) begin
      bit_idx <= 4'd0;
    end else if (scl_i_q == 1'b1 && scl_i == '0) begin
      bit_idx <= bit_idx + 1'b1;
    end else begin
      bit_idx <= bit_idx;
    end
  end

  // Deserializer for a byte read from the bus on the target side
  assign address0_match = ((input_byte[7:1] & target_mask0_i) == target_address0_i);
  assign address1_match = ((input_byte[7:1] & target_mask1_i) == target_address1_i);
  assign address_match = (address0_match || address1_match);
  assign rw_bit = input_byte[0];

  // Shift data in on positive SCL edge
  always_ff @ (posedge clk_i or negedge rst_ni) begin : tgt_input_register
    if (!rst_ni) begin
      input_byte <= 8'h00;
    end else if (input_byte_clr) begin
      input_byte <= 8'h00;
    end else if (scl_i_q == '0 && scl_i == 1'b1) begin
      if (!bit_ack) input_byte[7:0] <= {input_byte[6:0], sda_i};  // MSB goes in first
    end
  end

  // Detection by the target of ACK bit send by the host
  always_ff @ (posedge clk_i or negedge rst_ni) begin : host_ack_register
    if (!rst_ni) begin
      host_ack <= 1'b0;
    end else if (scl_i_q == '0 && scl_i == 1'b1) begin
      if (bit_ack) host_ack <= ~sda_i;
    end
  end

  // State definitions
  typedef enum logic [5:0] {
    Idle, PopFmtFifo, SetupStart, HoldStart, SetupStop, HoldStop,
        ClockLow, SetupBit, ClockPulse, HoldBit,
        ClockLowAck, SetupDevAck, ClockPulseAck, HoldDevAck,
        ReadClockLow, ReadSetupBit, ReadClockPulse, ReadHoldBit,
        HostClockLowAck, HostSetupBitAck, HostClockPulseAck, HostHoldBitAck,
        Active, ClockStart, ClockStop,
        AddrRead, AddrAckWait, AddrAckSetup, AddrAckPulse, AddrAckHold,
        TransmitWait, TransmitSetup, TransmitPulse, TransmitHold, TransmitAck,
        AcquireByte, AcquireAckWait, AcquireAckSetup, AcquireAckPulse, AcquireAckHold,
        PopTxFifo, StretchClock, AcquireSrP
  } state_e;

  state_e state_q, state_d;

  // Outputs for each state
  always_comb begin : state_outputs
    host_idle_o = 1'b1;
    target_idle_o = 1'b1;
    sda_temp = 1'b1;
    scl_temp = 1'b1;
    fmt_fifo_rready_o = 1'b0;
    rx_fifo_wvalid_o = 1'b0;
    rx_fifo_wdata_o = 8'h00;
    tx_fifo_rready_o = 1'b0;
    acq_fifo_wvalid_o = 1'b0;
    acq_fifo_wdata_o = 10'b0;
    event_nak_o = 1'b0;
    event_scl_interference_o = 1'b0;
    event_sda_interference_o = 1'b0;
    event_sda_unstable_o = 1'b0;
    event_stretch_timeout_o = 1'b0;
    event_trans_complete_o = 1'b0;
    event_tx_empty_o = 1'b0;
    event_tx_nonempty_o = 1'b0;
    event_ack_stop_o = 1'b0;
    unique case (state_q)
      // Idle: initial state, SDA and SCL are released (high)
      Idle : begin
        host_idle_o = 1'b1;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        if (host_enable_i && sda_i == '0) event_sda_interference_o = 1'b1;
        if (!target_address0_i && !target_mask0_i && !target_address1_i && !target_mask1_i) begin
          acq_fifo_wvalid_o = 1'b0;
        end
      end
      // SetupStart: SDA and SCL are released
      SetupStart : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        if (sda_i == '0) event_sda_interference_o = 1'b1;
        if (restart == 1'b1) event_trans_complete_o = 1'b1;
      end
      // HoldStart: SDA is pulled low, SCL is released
      HoldStart : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b1;
      end
      // ClockStart: SCL is pulled low, SDA stays low
      ClockStart : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b0;
      end
      // ClockLow: SCL is pulled low, SDA stays low
      ClockLow : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b0;
      end
      // SetupBit: Shift indexed bit onto SDA, SCL stays low
      SetupBit : begin
        host_idle_o = 1'b0;
        sda_temp = fmt_byte_i[bit_index];
        scl_temp = 1'b0;
        if (sda_temp == 1'b1 && sda_i == '0) event_sda_interference_o = 1'b1;
      end
      // ClockPulse: SCL is released, SDA keeps the indexed bit value
      ClockPulse : begin
        host_idle_o = 1'b0;
        sda_temp = fmt_byte_i[bit_index];
        scl_temp = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1'b1 && scl_i == '0)  event_scl_interference_o = 1'b1;
        if (sda_temp == 1'b1 && sda_i == '0) event_sda_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // HoldBit: SCL is pulled low
      HoldBit : begin
        host_idle_o = 1'b0;
        sda_temp = fmt_byte_i[bit_index];
        scl_temp = 1'b0;
        if (sda_temp == 1'b1 && sda_i == '0) event_sda_interference_o = 1'b1;
      end
      // ClockLowAck: SCL and SDA are pulled low
      ClockLowAck : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b0;
      end
      // SetupDevAck: SDA is released, waiting for target to pull it low
      SetupDevAck : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b0;
      end
      // ClockPulseAck: SCL is released
      ClockPulseAck : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        if (sda_i == '0 && !fmt_flag_nak_ok_i) event_nak_o = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1'b1 && scl_i == '0)  event_scl_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // HoldDevAck: SCL is pulled low
      HoldDevAck : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b0;
      end
      // ReadClockLow: SCL is pulled low, SDA is released
      ReadClockLow : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b0;
      end
      // ReadSetupBit: Read indexed bit off SDA, SCL stays low
      ReadSetupBit : begin
        host_idle_o = 1'b0;
        scl_temp = 1'b0;
      end
      // ReadClockPulse: SCL is released, the indexed bit value is read off SDA
      ReadClockPulse : begin
        host_idle_o = 1'b0;
        scl_temp = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1'b1 && scl_i == '0)  event_scl_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // ReadHoldBit: SCL is pulled low
      ReadHoldBit : begin
        host_idle_o = 1'b0;
        scl_temp = 1'b0;
        if (bit_index == '0 && tcount_q == 20'd1) begin
          rx_fifo_wdata_o = read_byte;  // transfer read data to rx_fifo
          rx_fifo_wvalid_o = 1'b1;      // assert that rx_fifo has valid data
        end
      end
      // HostClockLowAck: SCL and SDA are pulled low
      HostClockLowAck : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b0;
      end
      // HostSetupBitAck: Shift Ack/Nack bit onto SDA
      HostSetupBitAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_read_continue_i) sda_temp = 1'b0;
        else if (byte_index == 9'd1) sda_temp = 1'b1;
        else sda_temp = 1'b0;
        scl_temp = 1'b0;
        if (sda_temp == 1'b1 && sda_i == '0) event_sda_interference_o = 1'b1;
      end
      // HostClockPulseAck: SCL is released
      HostClockPulseAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_read_continue_i) sda_temp = 1'b0;
        else if (byte_index == 9'd1) sda_temp = 1'b1;
        else sda_temp = 1'b0;
        scl_temp = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1'b1 && scl_i == '0)  event_scl_interference_o = 1'b1;
        if (sda_temp == 1'b1 && sda_i == '0) event_sda_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // HostHoldBitAck: SCL is pulled low
      HostHoldBitAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_read_continue_i) sda_temp = 1'b0;
        else if (byte_index == 9'd1) sda_temp = 1'b1;
        else sda_temp = 1'b0;
        scl_temp = 1'b0;
        if (sda_temp == 1'b1 && sda_i == '0) event_sda_interference_o = 1'b1;
      end
      // ClockStop: SCL is pulled low, SDA stays low
      ClockStop : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b0;
      end
      // SetupStop: SDA is pulled low, SCL is released
      SetupStop : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b1;
      end
      // HoldStop: SDA and SCL are released
      HoldStop : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        if (sda_i == '0) event_sda_interference_o = 1'b1;
        event_trans_complete_o = 1'b1;
      end
      // Active: continue while keeping SCL low
      Active : begin
        host_idle_o = 1'b0;
        scl_temp = 1'b0;
      end
      // PopFmtFifo: populate fmt_fifo
      PopFmtFifo : begin
        host_idle_o = 1'b0;
        if (fmt_flag_stop_after_i) scl_temp = 1'b1;
        else scl_temp = 1'b0;
        fmt_fifo_rready_o = 1'b1;
      end
      // AddrRead: read and compare target address
      AddrRead : begin
        target_idle_o = 1'b0;
        if (bit_ack && address_match) begin
          acq_fifo_wdata_o = {1'b0, 1'b1, input_byte}; // transfer data to acq_fifo
          acq_fifo_wvalid_o = 1'b1;          // assert that acq_fifo has valid data
          if (tx_fifo_depth_i == '0 && rw_bit) event_tx_empty_o = 1'b1;
        end
      end
      // AddrAckWait: pause before acknowledging
      AddrAckWait : begin
        target_idle_o = 1'b0;
      end
      // AddrAckSetup: target pulls SDA low while SCL is low
      AddrAckSetup : begin
        target_idle_o = 1'b0;
        sda_temp = 1'b0;
      end
      // AddrAckPulse: target pulls SDA low while SCL is released
      AddrAckPulse : begin
        target_idle_o = 1'b0;
        sda_temp = 1'b0;
      end
      // AddrAckHold: target pulls SDA low while SCL is pulled low
      AddrAckHold : begin
        target_idle_o = 1'b0;
        sda_temp = 1'b0;
      end
      // TransmitWait: pause before sending a bit
      TransmitWait : begin
        target_idle_o = 1'b0;
      end
      // TransmitSetup: target shifts indexed bit onto SDA while SCL is low
      TransmitSetup : begin
        target_idle_o = 1'b0;
        sda_temp = tx_fifo_rdata_i[3'(bit_idx)];
      end
      // TransmitPulse: target shifts indexed bit onto SDA while SCL is released
      TransmitPulse : begin
        target_idle_o = 1'b0;
        sda_temp = tx_fifo_rdata_i[3'(bit_idx)];
      end
      // TransmitHold: target shifts indexed bit onto SDA while SCL is pulled low
      TransmitHold : begin
        target_idle_o = 1'b0;
        sda_temp = tx_fifo_rdata_i[3'(bit_idx)];
      end
      // TransmitAck: target waits for host to ACK transmission
      TransmitAck : begin
        target_idle_o = 1'b0;
        if (tx_fifo_depth_i == 6'd1 && !tx_fifo_wvalid_i && host_ack) event_tx_empty_o = 1'b1;
        if (host_ack && (start_det || stop_det)) event_ack_stop_o = 1'b1;
      end
      // PopTxFifo: populate tx_fifo
      PopTxFifo : begin
        target_idle_o = 1'b0;
        tx_fifo_rready_o = 1'b1;
      end
      // StretchClock: target stretches the clock
      StretchClock : begin
        target_idle_o = 1'b0;
        tx_fifo_rready_o = 1'b1;
        scl_temp = 1'b0;
        if (tx_fifo_depth_i == '0) event_tx_empty_o = 1'b1;
      end
      // AcquireByte: target acquires a byte
      AcquireByte : begin
        target_idle_o = 1'b0;
        if (bit_ack) begin
          acq_fifo_wdata_o = {1'b0, 1'b0, input_byte}; // transfer data to acq_fifo
          acq_fifo_wvalid_o = 1'b1;          // assert that acq_fifo has valid data
        end
      end
      // AcquireAckWait: pause before acknowledging
      AcquireAckWait : begin
        target_idle_o = 1'b0;
      end
      // AcquireAckSetup: target pulls SDA low while SCL is low
      AcquireAckSetup : begin
        target_idle_o = 1'b0;
        sda_temp = 1'b0;
      end
      // AcquireAckPulse: target pulls SDA low while SCL is released
      AcquireAckPulse : begin
        target_idle_o = 1'b0;
        sda_temp = 1'b0;
      end
      // AcquireAckHold: target pulls SDA low while SCL is pulled low
      AcquireAckHold : begin
        target_idle_o = 1'b0;
        sda_temp = 1'b0;
      end
      // AcquireSrP: target acquires repeated Start or Stop
      AcquireSrP : begin
        if (start_det) acq_fifo_wdata_o = {1'b1, 1'b1, input_byte};
        else acq_fifo_wdata_o = {1'b1, 1'b0, input_byte};
        acq_fifo_wvalid_o = 1'b1;
        if (tx_fifo_depth_i != '0) event_tx_nonempty_o = 1'b1;
      end
      // default
      default : begin
        host_idle_o = 1'b1;
        target_idle_o = 1'b1;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        fmt_fifo_rready_o = 1'b0;
        rx_fifo_wvalid_o = 1'b0;
        rx_fifo_wdata_o = 8'h00;
        tx_fifo_rready_o = 1'b0;
        acq_fifo_wvalid_o = 1'b0;
        acq_fifo_wdata_o = 10'b0;
        event_nak_o = 1'b0;
        event_scl_interference_o = 1'b0;
        event_sda_interference_o = 1'b0;
        event_sda_unstable_o = 1'b0;
        event_stretch_timeout_o = 1'b0;
        event_trans_complete_o = 1'b0;
        event_tx_empty_o = 1'b0;
        event_tx_nonempty_o = 1'b0;
        event_ack_stop_o = 1'b0;
      end
    endcase
  end

  // Conditional state transition
  always_comb begin : state_functions
    state_d = state_q;
    load_tcount = 1'b0;
    tcount_sel = tNoDelay;
    bit_decr = 1'b0;
    bit_clr = 1'b0;
    byte_decr = 1'b0;
    byte_clr = 1'b0;
    read_byte_clr = 1'b0;
    shift_data_en = 1'b0;
    log_start = 1'b0;
    log_stop = 1'b0;
    restart = 1'b0;
    input_byte_clr = 1'b0;

    unique case (state_q)
      // Idle: initial state, SDA and SCL are released (high)
      Idle : begin
        if (!host_enable_i && !target_enable_i) state_d = Idle; // Idle unless host is enabled
        else if (host_enable_i) begin
          if (!fmt_fifo_rvalid_i) state_d = Idle;
          else state_d = Active;
        end else if (target_enable_i) begin
          if (!start_det) state_d = Idle;
          else begin
            state_d = AddrRead;
            input_byte_clr = 1'b1;
          end
        end
      end

      // SetupStart: SDA and SCL are released
      SetupStart : begin
        if (no_stop) restart = 1'b1;
        if (tcount_q == 20'd1) begin
          state_d = HoldStart;
          load_tcount = 1'b1;
          tcount_sel = tHoldStart;
          log_start = 1'b1;
        end
      end
      // HoldStart: SDA is pulled low, SCL is released
      HoldStart : begin
        if (tcount_q == 20'd1) begin
          state_d = ClockStart;
          load_tcount = 1'b1;
          tcount_sel = tClockStart;
        end
      end
      // ClockStart: SCL is pulled low, SDA stays low
      ClockStart : begin
        if (tcount_q == 20'd1) begin
          state_d = ClockLow;
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
        end
      end

      // ClockLow: SCL is pulled low, SDA stays low
      ClockLow : begin
        if (tcount_q == 20'd1) begin
          state_d = SetupBit;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // SetupBit: Shift indexed bit onto SDA, SCL stays low
      SetupBit : begin
        if (tcount_q == 20'd1) begin
          state_d = ClockPulse;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ClockPulse: SCL is released, SDA keeps the indexed bit value
      ClockPulse : begin
        if (tcount_q == 20'd1) begin
          state_d = HoldBit;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
        end
      end
      // HoldBit: SCL is pulled low
      HoldBit : begin
        if (tcount_q == 20'd1) begin
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
          if (bit_index == '0) begin
            state_d = ClockLowAck;
            bit_clr = 1'b1;
          end else begin
            state_d = ClockLow;
            bit_decr = 1'b1;
          end
        end
      end

      // ClockLowAck: SCL and SDA are pulled low
      ClockLowAck : begin
        if (tcount_q == 20'd1) begin
          state_d = SetupDevAck;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // SetupDevAck: SDA is released, waiting for target to pull it low
      SetupDevAck : begin
        if (tcount_q == 20'd1) begin
          state_d = ClockPulseAck;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ClockPulseAck: SCL is released
      ClockPulseAck : begin
        if (tcount_q == 20'd1) begin
          state_d = HoldDevAck;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
        end
      end
      // HoldDevAck: SCL is pulled low
      HoldDevAck : begin
        if (tcount_q == 20'd1) begin
          if (fmt_flag_stop_after_i) begin
            state_d = ClockStop;
            load_tcount = 1'b1;
            tcount_sel = tClockStop;
          end else begin
            state_d = PopFmtFifo;
            load_tcount = 1'b1;
            tcount_sel = tNoDelay;
          end
        end
      end

      // ReadClockLow: SCL is pulled low, SDA is released
      ReadClockLow : begin
        if (tcount_q == 20'd1) begin
          state_d = ReadSetupBit;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // ReadSetupBit: Shift indexed bit onto SDA, SCL stays low
      ReadSetupBit : begin
        if (tcount_q == 20'd1) begin
          state_d = ReadClockPulse;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ReadClockPulse: SCL is released, the indexed bit value is read off SDA
      ReadClockPulse : begin
        if (tcount_q == 20'd1) begin
          state_d = ReadHoldBit;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
          shift_data_en = 1'b1;
        end
      end
      // ReadHoldBit: SCL is pulled low
      ReadHoldBit : begin
        if (tcount_q == 20'd1) begin
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
          if (bit_index == '0) begin
            state_d = HostClockLowAck;
            bit_clr = 1'b1;
            read_byte_clr = 1'b1;
          end else begin
            state_d = ReadClockLow;
            bit_decr = 1'b1;
          end
        end
      end

      // HostClockLowAck: SCL and SDA are pulled low
      HostClockLowAck : begin
        if (tcount_q == 20'd1) begin
          state_d = HostSetupBitAck;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // HostSetupBitAck: Shift Ack/Nack bit onto SDA
      HostSetupBitAck : begin
        if (tcount_q == 20'd1) begin
          state_d = HostClockPulseAck;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // HostClockPulseAck: SCL is released
      HostClockPulseAck : begin
        if (tcount_q == 20'd1) begin
          state_d = HostHoldBitAck;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
        end
      end
      // HostHoldBitAck: SCL is pulled low
      HostHoldBitAck : begin
        if (tcount_q == 20'd1) begin
          if (byte_index == 9'd1) begin
            if (fmt_flag_stop_after_i) begin
              state_d = ClockStop;
              load_tcount = 1'b1;
              tcount_sel = tClockStop;
            end else begin
              state_d = PopFmtFifo;
              load_tcount = 1'b1;
              tcount_sel = tNoDelay;
            end
          end else begin
            state_d = ReadClockLow;
            load_tcount = 1'b1;
            tcount_sel = tClockLow;
            byte_decr = 1'b1;
          end
        end
      end

      // ClockStop: SCL is pulled low, SDA stays low
      ClockStop : begin
        if (tcount_q == 20'd1) begin
          state_d = SetupStop;
          load_tcount = 1'b1;
          tcount_sel = tSetupStop;
        end
      end
      // SetupStop: SDA is pulled low, SCL is released
      SetupStop : begin
        if (tcount_q == 20'd1) begin
          state_d = HoldStop;
          load_tcount = 1'b1;
          tcount_sel = tHoldStop;
          log_stop = 1'b1;
        end
      end
      // HoldStop: SDA and SCL are released
      HoldStop : begin
        if (tcount_q == 20'd1) begin
          if (!host_enable_i) begin
            state_d = Idle;
            load_tcount = 1'b1;
            tcount_sel = tNoDelay;
          end else begin
            state_d = PopFmtFifo;
            load_tcount = 1'b1;
            tcount_sel = tNoDelay;
          end
        end
      end

      // Active: continue while keeping SCL low
      Active : begin
        if (fmt_flag_read_bytes_i) begin
          byte_clr = 1'b1;
          state_d = ReadClockLow;
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
        end else if (fmt_flag_start_before_i) begin
          state_d = SetupStart;
          load_tcount = 1'b1;
          tcount_sel = tSetupStart;
        end else begin
          state_d = ClockLow;
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
        end
      end

      // PopFmtFifo: populate fmt_fifo
      PopFmtFifo : begin
        if (!host_enable_i) begin
          state_d = ClockStop;
          load_tcount = 1'b1;
          tcount_sel = tClockStop;
        end else if (fmt_fifo_depth_i == 6'd1 && !fmt_fifo_wvalid_i) begin
          state_d = Idle;
          load_tcount = 1'b1;
          tcount_sel = tNoDelay;
        end else begin
          state_d = Active;
          load_tcount = 1'b1;
          tcount_sel = tNoDelay;
        end
      end

      // AddrRead: read and compare target address
      AddrRead : begin
        if (bit_ack) begin
          if (address_match) begin
            state_d = AddrAckWait;
            load_tcount = 1'b1;
            tcount_sel = tClockStart;
          end else state_d = Idle;
        end
      end

      // AddrAckWait: pause before acknowledging
      AddrAckWait : begin
        if (tcount_q == 20'd1) begin
          state_d = AddrAckSetup;
        end
      end
      // AddrAckSetup: target pulls SDA low while SCL is low
      AddrAckSetup : begin
        if (scl_i) state_d = AddrAckPulse;
      end
      // AddrAckPulse: target pulls SDA low while SCL is released
      AddrAckPulse : begin
        if (!scl_i) begin
          state_d = AddrAckHold;
          load_tcount = 1'b1;
          tcount_sel = tClockStart;
        end
      end
      // AddrAckHold: target pulls SDA low while SCL is pulled low
      AddrAckHold : begin
        if (tcount_q == 20'd1) begin
          if (rw_bit) begin
            if (tx_fifo_rvalid_i) begin
              state_d = TransmitWait;
              load_tcount = 1'b1;
              tcount_sel = tClockLow;
            end else state_d = StretchClock;
          end else state_d = AcquireByte;
        end
      end

      // TransmitWait: pause before sending a bit
      TransmitWait : begin
        if (tcount_q == 20'd1) begin
          state_d = TransmitSetup;
        end
      end
      // TransmitSetup: target shifts indexed bit onto SDA while SCL is low
      TransmitSetup : begin
        if (scl_i) state_d = TransmitPulse;
      end
      // TransmitPulse: target shifts indexed bit onto SDA while SCL is released
      TransmitPulse : begin
        if (!scl_i) begin
          state_d = TransmitHold;
          load_tcount = 1'b1;
          tcount_sel = tClockStart;
        end
      end
      // TransmitHold: target shifts indexed bit onto SDA while SCL is pulled low
      TransmitHold : begin
        if (tcount_q == 20'd1) begin
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
          if (bit_ack) begin
            state_d = TransmitAck;
          end else begin
            state_d = TransmitWait;
          end
        end
      end
      // TransmitAck: target waits for host to ACK transmission
      TransmitAck : begin
        if (scl_i) begin
          if (host_ack) state_d = PopTxFifo;
          else begin
            if (start_det || stop_det) state_d = AcquireSrP;
          end
        end
      end

      // PopTxFifo: populate tx_fifo
      PopTxFifo : begin
        if (!target_enable_i) begin
          state_d = Idle;
        end else if (tx_fifo_depth_i == 6'd1 && !tx_fifo_wvalid_i) begin
          state_d = StretchClock;
        end else begin
          state_d = TransmitWait;
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
        end
      end

      // StretchClock: target stretches the clock
      StretchClock : begin
        if (tx_fifo_depth_i == '0) begin
          state_d = StretchClock;
        end else begin
          state_d = TransmitWait;
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
        end
      end

      // AcquireByte: target acquires a byte
      AcquireByte : begin
        if (bit_ack) begin
          state_d = AcquireAckWait;
          load_tcount = 1'b1;
          tcount_sel = tClockStart;
        end
      end

      // AcquireAckWait: pause before acknowledging
      AcquireAckWait : begin
        if (tcount_q == 20'd1) begin
          state_d = AcquireAckSetup;
        end
      end
      // AcquireAckSetup: target pulls SDA low while SCL is low
      AcquireAckSetup : begin
        if (scl_i) state_d = AcquireAckPulse;
      end
      // AcquireAckPulse: target pulls SDA low while SCL is released
      AcquireAckPulse : begin
        if (!scl_i) begin
          state_d = AcquireAckHold;
          load_tcount = 1'b1;
          tcount_sel = tClockStart;
        end
      end
      // AcquireAckHold: target pulls SDA low while SCL is pulled low
      AcquireAckHold : begin
        if (tcount_q == 20'd1) begin
          if (bit_ack) begin
            if (start_det || stop_det) state_d = AcquireSrP;
            else state_d = AcquireByte;
          end
        end
      end

      // AcquireSrP: target acquires repeated Start or Stop
      AcquireSrP : begin
        state_d = Idle;
      end

      // default
      default : begin
        state_d = Idle;
        load_tcount = 1'b0;
        tcount_sel = tNoDelay;
        bit_decr = 1'b0;
        bit_clr = 1'b0;
        byte_decr = 1'b0;
        byte_clr = 1'b0;
        read_byte_clr = 1'b0;
        shift_data_en = 1'b0;
        log_start = 1'b0;
        log_stop = 1'b0;
        restart = 1'b0;
        input_byte_clr = 1'b0;
      end
    endcase
  end

  // Synchronous state transition
  always_ff @ (posedge clk_i or negedge rst_ni) begin : state_transition
    if (!rst_ni) begin
      state_q <= Idle;
    end else begin
      state_q <= state_d;
    end
  end

  // I2C bus outputs
  assign scl_o = scl_temp;
  assign sda_o = sda_temp;

endmodule
