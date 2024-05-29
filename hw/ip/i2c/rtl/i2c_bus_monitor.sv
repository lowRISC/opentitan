// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C bus idle and timeout monitoring, plus Start/Stop
// detection.

module i2c_bus_monitor import i2c_pkg::*;
(
  input                            clk_i,
  input                            rst_ni,

  input                            scl_i,
  input                            sda_i,

  input                            controller_enable_i,
  input                            multi_controller_enable_i,
  input                            target_enable_i,
  input                            target_idle_i,
  input [12:0]                     thd_dat_i,              // Data hold time(< 200 ns, < thd_sta)
  input [12:0]                     t_buf_i,                // Bus free time (< 5 us)
  input [29:0]                     bus_active_timeout_i,   // SCL held low  (~25 ms)
  input                            bus_active_timeout_en_i,
  input [19:0]                     bus_inactive_timeout_i, // SCL held high (~50 us)

  output logic                     bus_free_o,
  output                           start_detect_o,
  output                           stop_detect_o,

  output                           event_bus_active_timeout_o,
  output                           event_host_timeout_o

);

  // Only activate this monitor if at least one of the modules is enabled.
  logic monitor_enable, monitor_enable_q;
  assign monitor_enable = controller_enable_i | target_enable_i | multi_controller_enable_i;

  always_ff @ (posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      monitor_enable_q <= 1'b0;
    end else begin
      monitor_enable_q <= monitor_enable;
    end
  end

  // SDA and SCL at the previous clock edge
  logic scl_i_q, sda_i_q;
  always_ff @ (posedge clk_i or negedge rst_ni) begin : bus_prev
    if (!rst_ni) begin
      scl_i_q <= 1'b1;
      sda_i_q <= 1'b1;
    end else begin
      scl_i_q <= scl_i;
      sda_i_q <= sda_i;
    end
  end

  // Start and Stop detection
  //
  // To resolve ambiguity with early SDA arrival, reject control symbols when
  // SCL goes low too soon. The hold time for ordinary data/ACK bits is too
  // short to reliably see SCL change before SDA. Use the hold time for
  // control signals to ensure a Start or Stop symbol was actually received.
  // Requirements: thd_dat + 1 < thd_sta
  //   The extra (+1) here is to account for a late SDA arrival due to CDC
  //   skew.
  //
  // Note that this counter combines Start and Stop detection into one
  // counter. A controller-only reset scenario could end up with a Stop
  // following shortly after a Start, with the requisite setup time not
  // observed.
  logic        start_det_trigger, start_det_pending;
  logic        start_det;     // indicates start or repeated start is detected on the bus
  logic        stop_det_trigger, stop_det_pending;
  logic        stop_det;      // indicates stop is detected on the bus

  // Stop / Start detection counter
  logic [13:0] ctrl_det_count;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_det_count <= '0;
    end else if (start_det_trigger || stop_det_trigger) begin
      ctrl_det_count <= 14'd1;
    end else if (start_det_pending || stop_det_pending) begin
      ctrl_det_count <= ctrl_det_count + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_det_pending <= 1'b0;
    end else if (start_det_trigger) begin
      start_det_pending <= 1'b1;
    end else if (!monitor_enable || !scl_i || start_det || stop_det_trigger) begin
      start_det_pending <= 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stop_det_pending <= 1'b0;
    end else if (stop_det_trigger) begin
      stop_det_pending <= 1'b1;
    end else if (!monitor_enable || !scl_i || stop_det || start_det_trigger) begin
      stop_det_pending <= 1'b0;
    end
  end

  // (Repeated) Start condition detection by target
  assign start_det_trigger = monitor_enable && (scl_i_q && scl_i) & (sda_i_q && !sda_i);
  assign start_det = monitor_enable && start_det_pending && (ctrl_det_count >= 14'(thd_dat_i));
  assign start_detect_o = start_det;

  // Stop condition detection by target
  assign stop_det_trigger = monitor_enable && (scl_i_q && scl_i) & (!sda_i_q && sda_i);
  assign stop_det = monitor_enable && stop_det_pending && (ctrl_det_count >= 14'(thd_dat_i));
  assign stop_detect_o = stop_det;

  //
  // Bus timeout logic
  //

  // Detection of bus in a released state.
  logic bus_idling;
  assign bus_idling = scl_i && (sda_i == sda_i_q);

  logic [29:0] bus_release_cnt, bus_release_cnt_sel;
  logic bus_release_cnt_load, bus_release_cnt_dec;

  // bus_inactive_timeout_det is only high for the case where the bus release
  // counter reaches zero for bus idling, not the wait after a Stop condition.
  logic bus_inactive_timeout_det;

  logic bus_inactive_timeout_en;
  assign bus_inactive_timeout_en = (bus_inactive_timeout_i > '0);

  // bus_active_timeout latches high when SCL has been held low for too long.
  // This can be done intentionally or unintentionally, as the response for
  // target devices should be to abort the current transaction and release any
  // hold on the bus. Note that the bus doesn't immediately transition to
  // "free" status, since the controller can continue holding SCL low for some
  // time.
  logic bus_active_timeout_det_d, bus_active_timeout_det_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bus_active_timeout_det_q <= 1'b0;
    end else begin
      bus_active_timeout_det_q <= bus_active_timeout_det_d;
    end
  end

  // Bus release counter.
  // Together with the FSM below, this counter detects bus timeouts and the end
  // of the bus free time following a Stop condition.
  always_ff @ (posedge clk_i or negedge rst_ni) begin : bus_idle
    if (!rst_ni) begin
      bus_release_cnt <= '0;
    end else if (monitor_enable && !monitor_enable_q) begin
      // The rising edge of monitor enable resets the counter for
      // multi-controller mode.
      if (multi_controller_enable_i) begin
        // For the multi-controller case, wait until the bus isn't busy before
        // transmitting.
        bus_release_cnt <= 30'(bus_inactive_timeout_i);
      end
    end else if (bus_release_cnt_load) begin
      bus_release_cnt <= bus_release_cnt_sel;
    end else if (bus_release_cnt_dec && (bus_release_cnt != '0)) begin
      bus_release_cnt <= bus_release_cnt - 1'b1;
    end
  end

  typedef enum logic [1:0] {
    // Bus is currently free. Can transmit.
    StBusFree,
    // Bus is busy and not held with SCL high.
    StBusBusyLow,
    // Bus is currently busy, but SCL is held high.
    StBusBusyHigh,
    // Bus is currently busy, but saw a Stop. Count down to Bus Free.
    StBusBusyStop
  } bus_state_e;

  bus_state_e state_q, state_d;

  always_comb begin
    state_d = state_q;
    bus_release_cnt_load = 1'b0;
    bus_release_cnt_sel = 30'(t_buf_i);
    bus_release_cnt_dec = 1'b0;
    bus_inactive_timeout_det = 1'b0;
    bus_active_timeout_det_d = bus_active_timeout_det_q;

    unique case (state_q)
      StBusFree: begin
        bus_active_timeout_det_d = 1'b0;

        if (!scl_i || !sda_i) begin
          state_d = StBusBusyLow;
          bus_release_cnt_load = 1'b1;
          bus_release_cnt_sel = bus_active_timeout_i;
        end
      end

      StBusBusyLow: begin
        bus_release_cnt_dec = !scl_i;

        if (stop_det) begin
          state_d = StBusBusyStop;
          bus_release_cnt_load = 1'b1;
          bus_release_cnt_sel = 30'(t_buf_i);
        end else if (bus_idling && bus_inactive_timeout_en) begin
          state_d = StBusBusyHigh;
          bus_release_cnt_load = 1'b1;
          bus_release_cnt_sel = 30'(bus_inactive_timeout_i);
        end else if (scl_i) begin
          bus_release_cnt_load = 1'b1;
          bus_release_cnt_sel = bus_active_timeout_i;
          if (bus_active_timeout_det_q) begin
            // SCL was released due to the bus timeout, so go to BusFree.
            state_d = StBusFree;
          end
        end else if (bus_release_cnt == 30'd1) begin
          // The active timeout occurs when SCL has been held continuously low
          // for too long. Both the controller and target should respond to
          // this timeout and release the bus. We don't consider the bus free
          // yet, though: SCL must be released first.
          bus_active_timeout_det_d = bus_active_timeout_en_i;
        end
      end

      StBusBusyHigh: begin
        bus_release_cnt_dec = 1'b1;

        if (stop_det) begin
          state_d = StBusBusyStop;
          bus_release_cnt_load = 1'b1;
          bus_release_cnt_sel = 30'(t_buf_i);
        end else if (!bus_idling) begin
          state_d = StBusBusyLow;
          bus_release_cnt_load = 1'b1;
          bus_release_cnt_sel = bus_active_timeout_i;
        end else if (bus_release_cnt == 30'd1) begin
          // The host_timeout interrupt occurs regardless of which value of
          // SDA was present, but only transition to StBusFree if we entered
          // this state with SDA high. If SDA is low, a change to SCL will
          // cause a transition back to StBusBusyLow. If SDA changes from low
          // to high, we get a Stop condition and transition to StBusBusyStop.
          bus_inactive_timeout_det = bus_inactive_timeout_en;
          if (sda_i) begin
            state_d = StBusFree;
          end
        end
      end

      StBusBusyStop: begin
        bus_release_cnt_dec = 1'b1;

        if (!scl_i || !sda_i) begin
          state_d = StBusBusyLow;
        end else if (bus_release_cnt == 30'd1) begin
          state_d = StBusFree;
        end
      end

      default: begin
        state_d = StBusFree;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StBusFree;
    end else if (!monitor_enable) begin
      state_q <= StBusFree;
    end else if (monitor_enable && !monitor_enable_q) begin
      if (multi_controller_enable_i) begin
        // For the multi-controller case, wait until the bus isn't busy before
        // transmitting.
        state_q <= StBusBusyHigh;
      end else begin
        state_q <= StBusFree;
      end
    end else begin
      state_q <= state_d;
    end
  end

  always_comb begin
    if (multi_controller_enable_i) begin
      bus_free_o = (state_q == StBusFree);
    end else begin
      // For single-controller cases, the bus is only "busy" while waiting for the "bus free" time
      // after a Stop condition. In other words, that is the only time our controller can't
      // continue to the next transaction.
      bus_free_o = (state_q != StBusBusyStop);
    end
  end

  assign event_bus_active_timeout_o = bus_active_timeout_det_d && !bus_active_timeout_det_q;
  assign event_host_timeout_o = !target_idle_i && bus_inactive_timeout_det;

endmodule
