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

  input        fmt_fifo_rvalid_i, // indicates there is valid data in fmt_fifo
  output logic fmt_fifo_rready_o, // populates fmt_fifo
  input [7:0]  fmt_byte_i,        // byte in fmt_fifo to be sent to target
  input        fmt_flag_start_before_i, // issue start before sending byte
  input        fmt_flag_stop_after_i,   // issue stop after sending byte
  input        fmt_flag_read_bytes_i,   // indicates byte is an number of reads
  input        fmt_flag_read_continue_i,// host to send Ack to final byte read
  input        fmt_flag_nak_ok_i,       // no Ack is expected

  output logic       rx_fifo_wvalid_o, // high if there is valid data in rx_fifo
  output logic [7:0] rx_fifo_wdata_o,  // byte in rx_fifo read from target

  output logic       host_idle_o,      // indicates the host is idle

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

  output logic event_nak_o,              // target didn't Ack when expected
  output logic event_scl_interference_o, // other device forcing SCL low
  output logic event_sda_interference_o, // other device forcing SDA low
  output logic event_stretch_timeout_o,  // target stretches clock past max time
  output logic event_sda_unstable_o      // SDA is not constant during SCL pulse
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

  // Clock counter implementation
  typedef enum logic [3:0] {
    tSetupStart, tHoldStart, tClockLow, tSetupBit, tClockPulse, tHoldBit,
        tSetupStop, tHoldStop, tNoDelay
  } tcount_sel_e;

  tcount_sel_e tcount_sel;

  always_comb begin : counter_functions
    tcount_d = tcount_q;
    if (load_tcount) begin
      unique case (tcount_sel)
        tSetupStart : tcount_d = t_r_i + tsu_sta_i;
        tHoldStart  : tcount_d = t_f_i + thd_sta_i;
        tClockLow   : tcount_d = t_f_i + tlow_i - t_r_i - tsu_dat_i;
        tSetupBit   : tcount_d = t_r_i + tsu_dat_i;
        tClockPulse : tcount_d = t_r_i + thigh_i;
        tHoldBit    : tcount_d = t_f_i + thd_dat_i;
        tSetupStop  : tcount_d = t_r_i + tsu_sto_i;
        tHoldStop   : tcount_d = t_r_i + t_buf_i;
        tNoDelay    : tcount_d = '0;
        default     : tcount_d = '0;
      endcase
    end else if (stretch == 0) begin
      tcount_d = tcount_q - 1'b1;
    end else begin
      tcount_d = tcount_q;  // pause timer if clock is stretched
    end
  end

  always_ff @ (posedge clk_i or negedge rst_ni) begin : clk_counter
    if (!rst_ni) begin
      tcount_q <= '0;
    end else begin
      tcount_q <= tcount_d;
    end
  end

  // Clock stretching detection
  always_ff @ (posedge clk_i or negedge rst_ni) begin : clk_stretch
    if (!rst_ni) begin
      stretch <= '0;
    end else if (scl_temp == 1 && scl_i == 0) begin
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
    else if (fmt_byte_i == 0) byte_num = 9'd256;
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

  // State definitions
  typedef enum logic [4:0] {
    Idle, PopFmtFifo, SetupStart, HoldStart, SetupStop, HoldStop,
        ClockLow, SetupBit, ClockPulse, HoldBit,
        ClockLowAck, SetupDevAck, ClockPulseAck, HoldDevAck,
        ReadClockLow, ReadSetupBit, ReadClockPulse, ReadHoldBit,
        HostClockLowAck, HostSetupBitAck, HostClockPulseAck, HostHoldBitAck
  } state_e;

  state_e state_q, state_d;

  // Outputs for each state
  always_comb begin : state_outputs
    host_idle_o = 1'b1;
    sda_temp = 1'b1;
    scl_temp = 1'b1;
    fmt_fifo_rready_o = 1'b0;
    rx_fifo_wvalid_o = 1'b0;
    rx_fifo_wdata_o = 8'h00;
    event_nak_o = 1'b0;
    event_scl_interference_o = 1'b0;
    event_sda_interference_o = 1'b0;
    event_sda_unstable_o = 1'b0;
    event_stretch_timeout_o = 1'b0;
    unique case (state_q)
      // Idle: initial state, SDA and SCL are released (high)
      Idle : begin
        host_idle_o = 1'b1;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        if (sda_i == 0) event_sda_interference_o = 1'b1;
      end
      // SetupStart: SDA and SCL are released
      SetupStart : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        if (sda_i == 0) event_sda_interference_o = 1'b1;
      end
      // HoldStart: SDA is pulled low, SCL is released
      HoldStart : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
        scl_temp = 1'b1;
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
        if (sda_temp == 1 && sda_i == 0) event_sda_interference_o = 1'b1;
      end
      // ClockPulse: SCL is released, SDA keeps the indexed bit value
      ClockPulse : begin
        host_idle_o = 1'b0;
        sda_temp = fmt_byte_i[bit_index];
        scl_temp = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1 && scl_i == 0)  event_scl_interference_o = 1'b1;
        if (sda_temp == 1 && sda_i == 0) event_sda_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // HoldBit: SCL is pulled low
      HoldBit : begin
        host_idle_o = 1'b0;
        sda_temp = fmt_byte_i[bit_index];
        scl_temp = 1'b0;
        if (sda_temp == 1 && sda_i == 0) event_sda_interference_o = 1'b1;
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
        if (sda_i == 0 && !fmt_flag_nak_ok_i) event_nak_o = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1 && scl_i == 0)  event_scl_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // HoldDevAck: SCL is pulled low
      HoldDevAck : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b1;
        scl_temp = 1'b0;
      end
      // ReadClockLow: SCL is pulled low, SDA stays low
      ReadClockLow : begin
        host_idle_o = 1'b0;
        sda_temp = 1'b0;
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
        if (scl_i_q == 1 && scl_i == 0)  event_scl_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // ReadHoldBit: SCL is pulled low
      ReadHoldBit : begin
        host_idle_o = 1'b0;
        scl_temp = 1'b0;
        if (bit_index == 0 && tcount_q == 0) begin
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
        if (fmt_flag_stop_after_i && byte_index == 0) sda_temp = 1'b1;
        else if (fmt_flag_read_continue_i) sda_temp = 1'b0;
        else sda_temp = 1'b1;
        scl_temp = 1'b0;
        if (sda_temp == 1 && sda_i == 0) event_sda_interference_o = 1'b1;
      end
      // HostClockPulseAck: SCL is released
      HostClockPulseAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_stop_after_i && byte_index == 0) sda_temp = 1'b1;
        else if (fmt_flag_read_continue_i) sda_temp = 1'b0;
        else sda_temp = 1'b1;
        scl_temp = 1'b1;
        if ((stretch > stretch_timeout_i) && timeout_enable_i) begin
          event_stretch_timeout_o = 1'b1;
        end
        if (scl_i_q == 1 && scl_i == 0)  event_scl_interference_o = 1'b1;
        if (sda_temp == 1 && sda_i == 0) event_sda_interference_o = 1'b1;
        if (sda_i_q != sda_i)            event_sda_unstable_o = 1'b1;
      end
      // HostHoldBitAck: SCL is pulled low
      HostHoldBitAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_stop_after_i && byte_index == 0) sda_temp = 1'b1;
        else if (fmt_flag_read_continue_i) sda_temp = 1'b0;
        else sda_temp = 1'b1;
        scl_temp = 1'b0;
        if (sda_temp == 1 && sda_i == 0) event_sda_interference_o = 1'b1;
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
        if (sda_i == 0) event_sda_interference_o = 1'b1;
      end
      // PopFmtFifo: populates fmt_fifo
      PopFmtFifo : begin
        host_idle_o = 1'b0;
        fmt_fifo_rready_o = 1'b1;
      end
      // default
      default : begin
        host_idle_o = 1'b1;
        sda_temp = 1'b1;
        scl_temp = 1'b1;
        fmt_fifo_rready_o = 1'b0;
        rx_fifo_wvalid_o = 1'b0;
        rx_fifo_wdata_o = 8'h00;
        event_nak_o = 1'b0;
        event_scl_interference_o = 1'b0;
        event_sda_interference_o = 1'b0;
        event_sda_unstable_o = 1'b0;
        event_stretch_timeout_o = 1'b0;
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

    unique case (state_q)
      // Idle: initial state, SDA and SCL are released (high)
      Idle : begin
        if (!host_enable_i) state_d = Idle; // Idle unless host is enabled
        else if (!fmt_fifo_rvalid_i) state_d = Idle;
        else if (fmt_flag_read_bytes_i) begin
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

      // SetupStart: SDA and SCL are released
      SetupStart : begin
        if (tcount_q == 0) begin
          state_d = HoldStart;
          load_tcount = 1'b1;
          tcount_sel = tHoldStart;
        end
      end
      // HoldStart: SDA is pulled low, SCL is released
      HoldStart : begin
        if (tcount_q == 0) begin
          state_d = ClockLow;
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
        end
      end

      // ClockLow: SCL is pulled low, SDA stays low
      ClockLow : begin
        if (tcount_q == 0) begin
          state_d = SetupBit;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // SetupBit: Shift indexed bit onto SDA, SCL stays low
      SetupBit : begin
        if (tcount_q == 0) begin
          state_d = ClockPulse;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ClockPulse: SCL is released, SDA keeps the indexed bit value
      ClockPulse : begin
        if (tcount_q == 0) begin
          state_d = HoldBit;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
        end
      end
      // HoldBit: SCL is pulled low
      HoldBit : begin
        if (tcount_q == 0) begin
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
          if (bit_index == 0) begin
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
        if (tcount_q == 0) begin
          state_d = SetupDevAck;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // SetupDevAck: SDA is released, waiting for target to pull it low
      SetupDevAck : begin
        if (tcount_q == 0) begin
          state_d = ClockPulseAck;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ClockPulseAck: SCL is released
      ClockPulseAck : begin
        if (tcount_q == 0) begin
          state_d = HoldDevAck;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
        end
      end
      // HoldDevAck: SCL is pulled low
      HoldDevAck : begin
        if (tcount_q == 0) begin
          if (fmt_flag_stop_after_i) begin
            state_d = SetupStop;
            load_tcount = 1'b1;
            tcount_sel = tSetupStop;
          end else begin
            state_d = PopFmtFifo;
            load_tcount = 1'b1;
            tcount_sel = tNoDelay;
          end
        end
      end

      // ReadClockLow: SCL is pulled low, SDA stays low
      ReadClockLow : begin
        if (tcount_q == 0) begin
          state_d = ReadSetupBit;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // ReadSetupBit: Shift indexed bit onto SDA, SCL stays low
      ReadSetupBit : begin
        if (tcount_q == 0) begin
          state_d = ReadClockPulse;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ReadClockPulse: SCL is released, the indexed bit value is read off SDA
      ReadClockPulse : begin
        if (tcount_q == 0) begin
          state_d = ReadHoldBit;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
          shift_data_en = 1'b1;
        end
      end
      // ReadHoldBit: SCL is pulled low
      ReadHoldBit : begin
        if (tcount_q == 0) begin
          load_tcount = 1'b1;
          tcount_sel = tClockLow;
          if (bit_index == 0) begin
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
        if (tcount_q == 0) begin
          state_d = HostSetupBitAck;
          load_tcount = 1'b1;
          tcount_sel = tSetupBit;
        end
      end
      // HostSetupBitAck: Shift Ack/Nack bit onto SDA
      HostSetupBitAck : begin
        if (tcount_q == 0) begin
          state_d = HostClockPulseAck;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // HostClockPulseAck: SCL is released
      HostClockPulseAck : begin
        if (tcount_q == 0) begin
          state_d = HostHoldBitAck;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
        end
      end
      // HostHoldBitAck: SCL is pulled low
      HostHoldBitAck : begin
        if (tcount_q == 0) begin
          if (byte_index == 0) begin
            if (fmt_flag_stop_after_i) begin
              state_d = SetupStop;
              load_tcount = 1'b1;
              tcount_sel = tSetupStop;
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

      // SetupStop: SDA is pulled low, SCL is released
      SetupStop : begin
        if (tcount_q == 0) begin
          state_d = HoldStop;
          load_tcount = 1'b1;
          tcount_sel = tHoldStop;
        end
      end
      // HoldStop: SDA and SCL are released
      HoldStop : begin
        if (tcount_q == 0) begin
          state_d = PopFmtFifo;
          load_tcount = 1'b1;
          tcount_sel = tNoDelay;
        end
      end

      // PopFmtFifo: populates fmt_fifo
      PopFmtFifo : begin
        state_d = Idle;
        load_tcount = 1'b1;
        tcount_sel = tNoDelay;
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
