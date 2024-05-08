// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C finite state machine

module i2c_controller_fsm import i2c_pkg::*;
#(
  parameter int FifoDepth = 64,
  localparam int FifoDepthWidth = $clog2(FifoDepth+1)
) (
  input        clk_i,  // clock
  input        rst_ni, // active low reset

  input        scl_i,  // serial clock input from i2c bus
  output logic scl_o,  // serial clock output to i2c bus
  input        sda_i,  // serial data input from i2c bus
  output logic sda_o,  // serial data output to i2c bus
  input        bus_free_i,     // High if the bus is free for a new transmission
  output logic transmitting_o, // Controller is currently transmitting SDA

  input        host_enable_i,     // enable host functionality
  input        halt_controller_i, // Halt the controller FSM in Idle

  input                      fmt_fifo_rvalid_i, // indicates there is valid data in fmt_fifo
  input [FifoDepthWidth-1:0] fmt_fifo_depth_i,  // fmt_fifo_depth
  output logic               fmt_fifo_rready_o, // populates fmt_fifo
  input [7:0]                fmt_byte_i,        // byte in fmt_fifo to be sent to target
  input                      fmt_flag_start_before_i, // issue start before sending byte
  input                      fmt_flag_stop_after_i,   // issue stop after sending byte
  input                      fmt_flag_read_bytes_i,   // indicates byte is an number of reads
  input                      fmt_flag_read_continue_i,// host to send Ack to final byte read
  input                      fmt_flag_nak_ok_i,       // no Ack is expected
  input                      unhandled_unexp_nak_i,
  input                      unhandled_nak_timeout_i, // NACK handler timeout event not cleared

  output logic                     rx_fifo_wvalid_o, // high if there is valid data in rx_fifo
  output logic [RX_FIFO_WIDTH-1:0] rx_fifo_wdata_o,  // byte in rx_fifo read from target

  output logic       host_idle_o,      // indicates the host is idle

  input [12:0] thigh_i,    // high period of the SCL in clock units
  input [12:0] tlow_i,     // low period of the SCL in clock units
  input [12:0] t_r_i,      // rise time of both SDA and SCL in clock units
  input [12:0] t_f_i,      // fall time of both SDA and SCL in clock units
  input [12:0] thd_sta_i,  // hold time for (repeated) START in clock units
  input [12:0] tsu_sta_i,  // setup time for repeated START in clock units
  input [12:0] tsu_sto_i,  // setup time for STOP in clock units
  input [12:0] thd_dat_i,  // data hold time in clock units
  input        sda_interference_i, // High when SCL is high and SDA doesn't match while transmitting
  input [29:0] stretch_timeout_i,  // max time target connected to this host may stretch the clock
  input        timeout_enable_i,   // assert if target stretches clock past max
  input [30:0] host_nack_handler_timeout_i, // Timeout threshold for unhandled Host-Mode 'nak' irq.
  input        host_nack_handler_timeout_en_i,

  output logic event_nak_o,              // target didn't Ack when expected
  output logic event_unhandled_nak_timeout_o, // SW didn't handle the NACK in time
  output logic event_arbitration_lost_o, // Lost arbitration after beginning a transaction
  output logic event_scl_interference_o, // other device forcing SCL low
  output logic event_stretch_timeout_o,  // target stretches clock past max time
  output logic event_sda_unstable_o,     // SDA is not constant during SCL pulse
  output logic event_cmd_complete_o      // Command is complete
);

  // I2C bus clock timing variables
  logic [15:0] tcount_q;      // current counter for setting delays
  logic [15:0] tcount_d;      // next counter for setting delays
  logic        load_tcount;   // indicates counter must be loaded
  logic [30:0] stretch_idle_cnt; // counter for clock being stretched by target
                                 // or clock idle by host.
  logic [30:0] unhandled_nak_cnt; // In Host-mode, count cycles where the FSM is halted awaiting
                                  // the nak irq to be handled by SW.
  logic        incr_nak_cnt;

  // (IP in HOST-Mode) This bit is active when the FSM is in a state where a TARGET might
  // be trying to stretch the clock, preventing the controller FSM from continuing.
  logic        stretch_en;

  // Bit and byte counter variables
  logic [2:0]  bit_index;     // bit being transmitted to or read from the bus
  logic        bit_decr;      // indicates bit_index must be decremented by 1
  logic        bit_clr;       // indicates bit_index must be reset to 7
  logic [8:0]  byte_num;      // number of bytes to read
  logic [8:0]  byte_index;    // byte being read from the bus
  logic        byte_decr;     // indicates byte_index must be decremented by 1
  logic        byte_clr;      // indicates byte_index must be reset to byte_num

  // Other internal variables
  logic        scl_d;         // scl internal
  logic        sda_d;         // data internal
  logic        scl_i_q;       // scl_i delayed by one clock
  logic        sda_i_q;       // sda_i delayed by one clock
  logic [7:0]  read_byte;     // register for reads from target
  logic        read_byte_clr; // clear read_byte contents
  logic        shift_data_en; // indicates data must be shifted in from the bus
  logic        trans_started; // indicates a transaction has started
  logic        pend_restart;  // there is a pending restart waiting to be processed
  logic        req_restart;   // request restart
  logic        log_start;     // indicates start is been issued
  logic        log_stop;      // indicates stop is been issued
  logic        auto_stop_d, auto_stop_q; // Tracks whether a Stop symbol was autonomously generated.
  logic        ctrl_symbol_failed; // If SCL pulls low before the controller can issue Start/Stop

  // Clock counter implementation
  typedef enum logic [3:0] {
    tSetupStart,
    tHoldStart,
    tClockStart,
    tClockLow,
    tClockPulse,
    tClockHigh,
    tHoldBit,
    tClockStop,
    tSetupStop,
    tNoDelay
  } tcount_sel_e;

  tcount_sel_e tcount_sel;

  always_comb begin : counter_functions
    tcount_d = tcount_q;
    if (load_tcount) begin
      unique case (tcount_sel)
        tSetupStart : tcount_d = 13'(t_r_i) + 13'(tsu_sta_i);
        tHoldStart  : tcount_d = 13'(t_f_i) + 13'(thd_sta_i);
        tClockStart : tcount_d = 16'(thd_dat_i);
        tClockLow   : tcount_d = 13'(tlow_i) - 13'(thd_dat_i);
        tClockPulse : tcount_d = 13'(t_r_i) + 13'(thigh_i);
        tClockHigh  : tcount_d = 16'(thigh_i);
        tHoldBit    : tcount_d = 13'(t_f_i) + 13'(thd_dat_i);
        tClockStop  : tcount_d = 13'(t_f_i) + 13'(tlow_i) - 13'(thd_dat_i);
        tSetupStop  : tcount_d = 13'(t_r_i) + 13'(tsu_sto_i);
        tNoDelay    : tcount_d = 16'h0001;
        default     : tcount_d = 16'h0001;
      endcase
    end else if (
      host_enable_i ||
      // If we disable Host-Mode mid-txn, keep counting until the end of
      // byte, at which point we create a STOP condition then return to Idle.
      (!host_idle_o && !host_enable_i)) begin
      tcount_d = tcount_q - 1'b1;
    end
  end

  always_ff @ (posedge clk_i or negedge rst_ni) begin : clk_counter
    if (!rst_ni) begin
      tcount_q <= '1;
    end else begin
      tcount_q <= tcount_d;
    end
  end

  // Clock stretching/idle detection when i2c_ctrl.
  // When in host mode, this is a stretch count for how long an external target
  // has stretched the clock.
  // When in target mode, this is an idle count for how long an external host
  // has kept the clock idle after a START indication.
  always_ff @ (posedge clk_i or negedge rst_ni) begin : clk_stretch
    if (!rst_ni) begin
      stretch_idle_cnt <= '0;
    end else if (stretch_en && !scl_i) begin
      // HOST-mode count of clock stretching
      stretch_idle_cnt <= stretch_idle_cnt + 1'b1;
    end else begin
      stretch_idle_cnt <= '0;
    end
  end

  // The TARGET can stretch the clock during any time that the host drives SCL to 0.
  // However, we (the HOST) cannot know it is being stretched until we release SCL,
  // usually trying to create the next clock pulse.
  // There is a minimum 3-cycle round trip (1-cycle output flop, 2-cycle input synchronizer),
  // between releasing the clock and observing the effect of releasing the clock on
  // the inputs. However, this is really '1 + t_r + 2' as the bus also needs to slew to '1
  // before can observe it. Even if the TARGET is not stretching the clock, we cannot
  // confirm it until at-least this amount of time has elapsed.
  //
  // 'stretch_predict_cnt_expired' becomes active once we have observed (4 + t_r) cycles of
  // delay, and if !scl_i at this point we know that the TARGET is stretching the clock.
  // > This implementation requires 'thigh >= 4' to guarantee we don't miss stretching.
  logic [30:0] stretch_cnt_threshold;
  assign stretch_cnt_threshold = 31'd2 + 31'(t_r_i);

  logic stretch_predict_cnt_expired;
  always_ff @ (posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stretch_predict_cnt_expired <= 1'b0;
    end else begin
      if (stretch_idle_cnt == stretch_cnt_threshold) begin
        stretch_predict_cnt_expired <= 1'b1;
      end else if (!stretch_en) begin
        stretch_predict_cnt_expired <= 1'b0;
      end
    end
  end

  // While the FSM is halted due to an unhandled 'nak' irq in Host-Mode, this counter can
  // be used to trigger a timeout which disables Host-Mode and creates a STOP condition to
  // end the transaction.
  logic unhandled_nak_cnt_expired;
  always_ff @ (posedge clk_i or negedge rst_ni) begin : unhandled_nak_cnt_b
    if (!rst_ni) begin
      unhandled_nak_cnt <= '0;
      unhandled_nak_cnt_expired <= 1'b0;
    end else if (incr_nak_cnt) begin
      // Increment the counter while the FSM is halted in Idle.
      unhandled_nak_cnt <= unhandled_nak_cnt + 1'b1;
      if (unhandled_nak_cnt > host_nack_handler_timeout_i) begin
        unhandled_nak_cnt_expired <= 1'b1;
      end
    end else begin
      unhandled_nak_cnt <= '0;
      unhandled_nak_cnt_expired <= 1'b0;
    end
  end

  assign event_unhandled_nak_timeout_o = unhandled_nak_cnt_expired;

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

  // SCL going low early is just clock synchronization. SCL switching so fast that the controller
  // can't even sense its outputs is cause for a bus error.
  assign event_arbitration_lost_o = event_sda_unstable_o || sda_interference_i ||
                                    ctrl_symbol_failed;

  // Registers whether a transaction start has been observed.
  // A transaction start does not include a "restart", but rather
  // the first start after enabling i2c, or a start observed after a
  // stop.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      trans_started <= '0;
    end else if (trans_started && (!host_enable_i || event_arbitration_lost_o)) begin
      trans_started <= '0;
    end else if (log_start) begin
      trans_started <= 1'b1;
    end else if (log_stop) begin
      trans_started <= 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pend_restart <= '0;
    end else if (pend_restart && !host_enable_i) begin
      pend_restart <= '0;
    end else if (req_restart) begin
      pend_restart <= 1'b1;
    end else if (log_start) begin
      pend_restart <= '0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      auto_stop_q <= 1'b0;
    end else begin
      auto_stop_q <= auto_stop_d;
    end
  end

  // State definitions
  typedef enum logic [4:0] {
    Idle,
    ///////////////////////
    // Host function states
    ///////////////////////
    Active, PopFmtFifo,
    // Host function starts a transaction
    SetupStart, HoldStart, ClockStart,
    // Host function stops a transaction
    SetupStop, HoldStop, ClockStop,
    // Host function transmits a bit to the external target
    ClockLow, ClockPulse, HoldBit,
    // Host function recevies an ack from the external target
    ClockLowAck, ClockPulseAck, HoldDevAck,
    // Host function reads a bit from the external target
    ReadClockLow, ReadClockPulse, ReadHoldBit,
    // Host function transmits an ack to the external target
    HostClockLowAck, HostClockPulseAck, HostHoldBitAck
  } state_e;

  state_e state_q, state_d;


  // Increment the NACK timeout count if the controller is halted in Idle and
  // the timeout hasn't yet occurred.
  assign incr_nak_cnt = unhandled_unexp_nak_i && host_enable_i && (state_q == Idle) &&
                        host_nack_handler_timeout_en_i && !unhandled_nak_timeout_i;

  // Outputs for each state
  always_comb begin : state_outputs
    host_idle_o = 1'b1;
    sda_d = 1'b1;
    scl_d = 1'b1;
    transmitting_o = 1'b0;
    log_start = 1'b0;
    log_stop = 1'b0;
    fmt_fifo_rready_o = 1'b0;
    rx_fifo_wvalid_o = 1'b0;
    rx_fifo_wdata_o = RX_FIFO_WIDTH'(0);
    event_nak_o = 1'b0;
    event_scl_interference_o = 1'b0;
    ctrl_symbol_failed = 1'b0;
    event_sda_unstable_o = 1'b0;
    event_cmd_complete_o = 1'b0;
    stretch_en = 1'b0;
    unique case (state_q)
      // Idle: initial state, SDA is released (high), SCL is released if the
      // bus is idle. Otherwise, if no STOP condition has been sent yet,
      // continue pulling SCL low in host mode.
      Idle : begin
        sda_d = 1'b1;
        if (trans_started) begin
          host_idle_o = 1'b0;
          scl_d = 1'b0;
        end else begin
          host_idle_o = 1'b1;
          scl_d = 1'b1;
        end
      end

      ///////////////
      // HOST MODE //
      ///////////////

      // SetupStart: SDA and SCL are released
      SetupStart : begin
        host_idle_o = 1'b0;
        sda_d = 1'b1;
        scl_d = 1'b1;
        transmitting_o = 1'b1;
        // If this is a restart, SCL was last low, and a target could be stretching the clock.
        stretch_en = trans_started;
        if (trans_started && !scl_i && scl_i_q) begin
          // If this is a repeated Start, an early clock prevents issuing the symbol. If it's not
          // a repeated start, the FSM will just go back to Idle and wait for the bus to go free
          // again.
          ctrl_symbol_failed = 1'b1;
        end else if (tcount_q == 20'd1) begin
          log_start = 1'b1;
          event_cmd_complete_o = pend_restart;
        end
      end
      // HoldStart: SDA is pulled low, SCL is released
      HoldStart : begin
        host_idle_o = 1'b0;
        sda_d = 1'b0;
        scl_d = 1'b1;
        transmitting_o = 1'b1;
        if (scl_i_q && !scl_i)  event_scl_interference_o = 1'b1;
      end
      // ClockStart: SCL is pulled low, SDA stays low
      ClockStart : begin
        host_idle_o = 1'b0;
        sda_d = 1'b0;
        scl_d = 1'b0;
        transmitting_o = 1'b1;
      end
      ClockLow : begin
        host_idle_o = 1'b0;
        if (pend_restart) begin
          sda_d = 1'b1;
        end else begin
          sda_d = fmt_byte_i[bit_index];
        end
        scl_d = 1'b0;
        transmitting_o = 1'b1;
      end
      // ClockPulse: SCL is released, SDA keeps the indexed bit value
      ClockPulse : begin
        host_idle_o = 1'b0;
        sda_d = fmt_byte_i[bit_index];
        scl_d = 1'b1;
        transmitting_o = 1'b1;
        stretch_en = 1'b1;
        if (scl_i_q && !scl_i)  event_scl_interference_o = 1'b1;
        if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          event_sda_unstable_o = 1'b1;
        end
      end
      // HoldBit: SCL is pulled low
      HoldBit : begin
        host_idle_o = 1'b0;
        sda_d = fmt_byte_i[bit_index];
        scl_d = 1'b0;
        transmitting_o = 1'b1;
      end
      // ClockLowAck: SCL pulled low, SDA is released
      ClockLowAck : begin
        host_idle_o = 1'b0;
        sda_d = 1'b1;
        scl_d = 1'b0;
      end
      // ClockPulseAck: SCL is released
      ClockPulseAck : begin
        host_idle_o = 1'b0;
        sda_d = 1'b1;
        scl_d = 1'b1;
        if (!scl_i_q && scl_i && sda_i && !fmt_flag_nak_ok_i) event_nak_o = 1'b1;
        stretch_en = 1'b1;
        if (scl_i_q && !scl_i)  event_scl_interference_o = 1'b1;
        if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          event_sda_unstable_o = 1'b1;
        end
      end
      // HoldDevAck: SCL is pulled low
      HoldDevAck : begin
        host_idle_o = 1'b0;
        sda_d = 1'b1;
        scl_d = 1'b0;
      end
      // ReadClockLow: SCL is pulled low, SDA is released
      ReadClockLow : begin
        host_idle_o = 1'b0;
        sda_d = 1'b1;
        scl_d = 1'b0;
      end
      // ReadClockPulse: SCL is released, the indexed bit value is read off SDA
      ReadClockPulse : begin
        host_idle_o = 1'b0;
        scl_d = 1'b1;
        stretch_en = 1'b1;
        if (scl_i_q && !scl_i)  event_scl_interference_o = 1'b1;
        if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          event_sda_unstable_o = 1'b1;
        end
      end
      // ReadHoldBit: SCL is pulled low
      ReadHoldBit : begin
        host_idle_o = 1'b0;
        scl_d = 1'b0;
        if (bit_index == '0 && tcount_q == 20'd1) begin
          rx_fifo_wvalid_o = 1'b1;      // assert that rx_fifo has valid data
          rx_fifo_wdata_o = read_byte;  // transfer read data to rx_fifo
        end
      end
      // HostClockLowAck: SCL pulled low, SDA is conditional
      HostClockLowAck : begin
        host_idle_o = 1'b0;
        scl_d = 1'b0;
        transmitting_o = 1'b1;

        // If it is the last byte of a read, send a NAK before the stop.
        // Otherwise send the ack.
        if (fmt_flag_read_continue_i) sda_d = 1'b0;
        else if (byte_index == 9'd1) sda_d = 1'b1;
        else sda_d = 1'b0;
      end
      // HostClockPulseAck: SCL is released
      HostClockPulseAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_read_continue_i) sda_d = 1'b0;
        else if (byte_index == 9'd1) sda_d = 1'b1;
        else sda_d = 1'b0;
        scl_d = 1'b1;
        transmitting_o = 1'b1;
        stretch_en = 1'b1;
        if (scl_i_q && !scl_i)  event_scl_interference_o = 1'b1;
        if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          event_sda_unstable_o = 1'b1;
        end
      end
      // HostHoldBitAck: SCL is pulled low
      HostHoldBitAck : begin
        host_idle_o = 1'b0;
        if (fmt_flag_read_continue_i) sda_d = 1'b0;
        else if (byte_index == 9'd1) sda_d = 1'b1;
        else sda_d = 1'b0;
        scl_d = 1'b0;
        transmitting_o = 1'b1;
      end
      // ClockStop: SCL is pulled low, SDA stays low
      ClockStop : begin
        host_idle_o = 1'b0;
        sda_d = 1'b0;
        scl_d = 1'b0;
        transmitting_o = 1'b1;
      end
      // SetupStop: SDA is pulled low, SCL is released
      SetupStop : begin
        host_idle_o = 1'b0;
        sda_d = 1'b0;
        scl_d = 1'b1;
        transmitting_o = 1'b1;
        stretch_en = 1'b1;
        if (!scl_i && scl_i_q) begin
          // Failed to issue Stop before some other device could pull SCL low.
          ctrl_symbol_failed = 1'b1;
        end
      end
      // HoldStop: SDA and SCL are released
      HoldStop : begin
        host_idle_o = 1'b0;
        sda_d = 1'b1;
        scl_d = 1'b1;
        event_cmd_complete_o = 1'b1;
        if (!sda_i && !scl_i) begin
          // Failed to issue Stop before some other device could pull SCL low.
          ctrl_symbol_failed = 1'b1;
        end else if (sda_i) begin
          log_stop = 1'b1;
        end
      end
      // Active: continue while keeping SCL low
      Active : begin
        host_idle_o = 1'b0;

        // If this is a transaction start, do not drive scl low
        // since in the next state we will drive it high to initiate
        // the start bit.
        // If this is a restart, continue driving the clock low.
        scl_d = fmt_flag_start_before_i && !trans_started;
      end
      // PopFmtFifo: populate fmt_fifo
      PopFmtFifo : begin
        host_idle_o = 1'b0;
        if (fmt_flag_stop_after_i) scl_d = 1'b1;
        else scl_d = 1'b0;
        fmt_fifo_rready_o = 1'b1;
      end

      // default
      default : begin
        host_idle_o = 1'b1;
        sda_d = 1'b1;
        scl_d = 1'b1;
        transmitting_o = 1'b0;
        log_start = 1'b0;
        log_stop = 1'b0;
        event_scl_interference_o = 1'b0;
        ctrl_symbol_failed = 1'b0;
        fmt_fifo_rready_o = 1'b0;
        rx_fifo_wvalid_o = 1'b0;
        rx_fifo_wdata_o = RX_FIFO_WIDTH'(0);
        event_nak_o = 1'b0;
        event_sda_unstable_o = 1'b0;
        event_cmd_complete_o = 1'b0;
      end
    endcase // unique case (state_q)
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
    req_restart = 1'b0;
    auto_stop_d = auto_stop_q;

    unique case (state_q)
      // Idle: initial state, SDA is released (high), and SCL is released if there is no ongoing
      // transaction.
      Idle : begin
        if (host_enable_i) begin
          if (unhandled_unexp_nak_i || unhandled_nak_timeout_i || halt_controller_i) begin
            // If we are awaiting software to handle an unexpected NACK, halt the FSM here.
            // The current transaction does not end, and SCL remains in its current state.
            // Software typically should handle an unexpected NACK by either disabling the
            // controller (causing host_enable_i to fall) or by the following sequence:
            //   1. Clear and/or populate the FMT FIFO.
            //   2. Clear CONTROLLER_EVENTS.NACK
            // Note that if the timeout feature is enabled, the controller will be forced to
            // issue a Stop if software takes too long to address the NACK. A short timeout
            // could also be used to automatically issue a Stop whenever an unexpected NACK
            // occurs.
            // Note that we may also halt here on a bus timeout or if arbitration was lost, so
            // software may fix up the FIFOs before beginning a new transaction.
            if (trans_started && unhandled_nak_cnt_expired) begin
              // If our timeout counter expires, generate a STOP condition automatically.
              auto_stop_d = 1'b1;
              state_d = ClockStop;
              load_tcount = 1'b1;
              tcount_sel = tClockStop;
            end
          end else if (fmt_fifo_rvalid_i) begin
            if (trans_started || bus_free_i) begin
              state_d = Active;
            end
          end
        end else if (trans_started && !host_enable_i) begin
            auto_stop_d = 1'b1;
            state_d = ClockStop;
            load_tcount = 1'b1;
            tcount_sel = tClockStop;
        end
      end

      ///////////////
      // HOST MODE //
      ///////////////

      // SetupStart: SDA and SCL are released
      SetupStart : begin
        if (!trans_started && !scl_i) begin
          // This was the start of a transaction, but another device beat us to access. Go back to
          // Idle, and wait for the next turn.
          state_d = Idle;
        end else if (trans_started && !scl_i && !scl_i_q && stretch_predict_cnt_expired) begin
          // Saw stretching. Remain in this state and don't count down until we see SCL high.
          state_d = SetupStart;
          load_tcount = 1'b1;
          // This double-counts the rise time, unfortunately.
          tcount_sel = tSetupStart;
        end else if (trans_started && !scl_i && scl_i_q) begin
          // Failed to issue repeated Start. Effectively lost arbitration.
          state_d = Idle;
        end else if (tcount_q == 20'd1) begin
          state_d = HoldStart;
          load_tcount = 1'b1;
          tcount_sel = tHoldStart;
        end
      end
      // HoldStart: SDA is pulled low, SCL is released
      HoldStart : begin
        if (tcount_q == 20'd1 || (!scl_i && scl_i_q)) begin
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
      // ClockLow: SCL stays low, shift indexed bit onto SDA
      ClockLow : begin
        if (tcount_q == 20'd1) begin
          load_tcount = 1'b1;
          if (pend_restart) begin
            state_d = SetupStart;
            tcount_sel = tSetupStart;
          end else begin
            state_d = ClockPulse;
            tcount_sel = tClockPulse;
          end
        end
      end
      // ClockPulse: SCL is released, SDA keeps the indexed bit value
      ClockPulse : begin
        if (!scl_i && !scl_i_q && stretch_predict_cnt_expired) begin
          // Saw stretching. Remain in this state and don't count down until we see SCL high.
          load_tcount = 1'b1;
          tcount_sel = tClockHigh;
        end else if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          state_d = Idle;
        end else if (tcount_q == 20'd1 || (!scl_i && scl_i_q)) begin
          // Transition either when we finish counting our high period or
          // another controller pulls clock low.
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
      // ClockLowAck: Target is allowed to drive ack back
      // to host (dut)
      ClockLowAck : begin
        if (tcount_q == 20'd1) begin
          state_d = ClockPulseAck;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ClockPulseAck: SCL is released
      ClockPulseAck : begin
        if (!scl_i && !scl_i_q && stretch_predict_cnt_expired) begin
          // Saw stretching. Remain in this state and don't count down until we see SCL high.
          load_tcount = 1'b1;
          tcount_sel = tClockHigh;
        end else if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          state_d = Idle;
        end else begin
          if (tcount_q == 20'd1 || (!scl_i && scl_i_q)) begin
            state_d = HoldDevAck;
            load_tcount = 1'b1;
            tcount_sel = tHoldBit;
          end
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
          state_d = ReadClockPulse;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // ReadClockPulse: SCL is released, the indexed bit value is read off SDA
      ReadClockPulse : begin
        if (!scl_i && !scl_i_q && stretch_predict_cnt_expired) begin
          // Saw stretching. Remain in this state and don't count down until we see SCL high.
          load_tcount = 1'b1;
          tcount_sel = tClockHigh;
        end else if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          state_d = Idle;
        end else if (tcount_q == 20'd1 || (!scl_i && scl_i_q)) begin
          state_d = ReadHoldBit;
          load_tcount = 1'b1;
          tcount_sel = tHoldBit;
          shift_data_en = 1'b1; // SDA is sampled on the final clk_i cycle of the SCL pulse.
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
      // HostClockLowAck: SCL is pulled low, SDA is conditional based on
      // byte position
      HostClockLowAck : begin
        if (tcount_q == 20'd1) begin
          state_d = HostClockPulseAck;
          load_tcount = 1'b1;
          tcount_sel = tClockPulse;
        end
      end
      // HostClockPulseAck: SCL is released
      HostClockPulseAck : begin
        if (!scl_i && !scl_i_q && stretch_predict_cnt_expired) begin
          // Saw stretching. Remain in this state and don't count down until we see SCL high.
          load_tcount = 1'b1;
          tcount_sel = tClockHigh;
        end else if (scl_i_q && scl_i && (sda_i_q != sda_i)) begin
          // Unexpected Stop / Start
          state_d = Idle;
        end else if (tcount_q == 20'd1 || (!scl_i && scl_i_q)) begin
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
        if (!scl_i && !scl_i_q && stretch_predict_cnt_expired) begin
          // Saw stretching. Remain in this state and don't count down until we see SCL high.
          load_tcount = 1'b1;
          tcount_sel = tSetupStop;
        end else if (!scl_i && scl_i_q) begin
          // Failed to issue Stop before some other device could pull SCL low.
          state_d = Idle;
        end else if (tcount_q == 20'd1) begin
          state_d = HoldStop;
        end
      end
      // HoldStop: SDA and SCL are released
      HoldStop : begin
        if (!sda_i && !scl_i) begin
          // Failed to issue Stop before some other device could pull SCL low.
          state_d = Idle;
          auto_stop_d = 1'b0;
        end else if (sda_i) begin
          auto_stop_d = 1'b0;
          if (auto_stop_q) begin
            // If this Stop symbol was generated automatically, go back to Idle.
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
        end else if (fmt_flag_start_before_i && !trans_started) begin
          state_d = SetupStart;
          load_tcount = 1'b1;
          tcount_sel = tSetupStart;
        end else begin
          state_d = ClockLow;
          load_tcount = 1'b1;
          req_restart = fmt_flag_start_before_i;
          tcount_sel = tClockLow;
        end
      end
      // PopFmtFifo: pop fmt_fifo item
      PopFmtFifo : begin
        if (!host_enable_i && trans_started) begin
          auto_stop_d = 1'b1;
          state_d = ClockStop;
          load_tcount = 1'b1;
          tcount_sel = tClockStop;
        end else if (!host_enable_i || (fmt_fifo_depth_i == 7'h1) ||
                     unhandled_unexp_nak_i || !trans_started) begin
          state_d = Idle;
          load_tcount = 1'b1;
          tcount_sel = tNoDelay;
        end else begin
          state_d = Active;
          load_tcount = 1'b1;
          tcount_sel = tNoDelay;
        end
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
        auto_stop_d = 1'b0;
      end
    endcase // unique case (state_q)

    if (trans_started && (sda_interference_i || ctrl_symbol_failed)) begin
      state_d = Idle;
    end
  end

  // Synchronous state transition
  always_ff @ (posedge clk_i or negedge rst_ni) begin : state_transition
    if (!rst_ni) begin
      state_q <= Idle;
    end else begin
      state_q <= state_d;
    end
  end

  assign scl_o = scl_d;
  assign sda_o = sda_d;

  // Target stretched clock beyond timeout
  assign event_stretch_timeout_o = stretch_en && timeout_enable_i &&
                                   (stretch_idle_cnt > 31'(stretch_timeout_i));

  // Make sure we never attempt to send a single cycle glitch
  `ASSERT(SclOutputGlitch_A, $rose(scl_o) |-> ##1 scl_o)

  // TODO: Handle the assertion below
//  // I2C bus outputs
//  always_ff @(posedge clk_i or negedge rst_ni) begin
//    if (!rst_ni) begin
//      scl_q <= 1'b1;
//      sda_q <= 1'b1;
//    end else begin
//      scl_q <= scl_d;
//      sda_q <= sda_d;
//    end
//  end
//
//  // Check that we don't change SCL and SDA in the same clock cycle in host mode.
//  `ASSERT(SclSdaChangeNotSimultaneous_A, !(host_enable_i && (scl_d != scl_q) && (sda_d != sda_q)))

endmodule
