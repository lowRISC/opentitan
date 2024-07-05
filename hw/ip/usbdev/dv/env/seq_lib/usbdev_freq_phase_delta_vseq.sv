// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Frequency and phase delta between host and device.
//
// - Host and DUT frequency may be set independently, to opposite extremes of the permitted
//   frequency range if desired.
// - DUT frequency may be adjusted in response to the DUT timing reference signal to match the
//   frequency of the host.
// - Host frequency may be configured to drift throughout the test.
// - Sequence may execute with or without traffic (max length packets to increase the likelihood
//   of sampling errors from frequency/phase mismatch).
// - There is a 10ms 'Reset Recovery' period guaranteed within the USB 2.0 protocol specification,
//   during which the host controller is not permitted to send anything other than SOF packets
//   to the DUT; this is important in guaranteeing that the DUT has time to measure and track the
//   frequency of the host.
class usbdev_freq_phase_delta_vseq extends usbdev_stream_len_max_vseq;
  `uvm_object_utils(usbdev_freq_phase_delta_vseq)

  `uvm_object_new

  // Min/max DUT clock frequencies (scaled from 12Mbps to 48MHz clock) according to the
  // USB 2.0 specification; Table 7-9.
  localparam uint USB_CLK_FREQ_MIN_KHZ = 4 * 11_970;
  localparam uint USB_CLK_FREQ_MAX_KHZ = 4 * 12_030;

  // Target number of clock cycles per bus frame.
  localparam int CYCLES_PER_FRAME = 48_000;

  // Duration of test in 1ms bus frames.
  rand uint num_frames;
  constraint num_frames_c {
    num_frames inside {[80:120]};
  }

  // Target clock frequency of host.
  rand uint host_target_freq_khz;
  constraint host_target_freq_khz_c {
    // Maximum frequency extremes, since the host is using the same oversampling scheme as the DUT.
    // See USB 2.0 Table 7-9.
    host_target_freq_khz >= USB_CLK_FREQ_MIN_KHZ && host_target_freq_khz <= USB_CLK_FREQ_MAX_KHZ;
  }

  // Configured initial frequency deltas from 48Mhz, given in Hz.
  int host_freq_delta;
  int usb_freq_delta;

  // Are we required to track the host frequency by adjusting the DUT oscillator?
  bit osc_tracking = 0;

  // Shall the host clock frequency drift over the duration of the test?
  bit host_drifting = 0;

  // Shall there be any bus traffic during this test?
  bit with_traffic = 1;

  // Observe Reset Recovery period; do not transmit anything other than SOF packets within 10ms
  // of Reset Signaling?
  bit reset_recovery = 1;

  // Test only SOF reception, not maximum length packets; diagnostic/development switch can make
  // it easier to study the frequency drifting/tracking.
  bit sof_only = 0;

  // Indicates that all test frames have completed; the test sequence is terminating.
  bit all_frames_done = 0;

  // Is transmission of regular bus traffic presently permitted?
  //   (This prevents collision with the SOF packet at the start of each bus frame.)
  bit can_transmit = 0;

  // Count of the number of SOF packets sent since the last Bus Reset; this is used to ascertain
  // when the 'reset recovery' period has elapsed.
  int unsigned sof_sent = 0;

  // Drift the host clock frequency
  virtual task host_drift();
    // Sample the current host frequency and the total intended drift.
    int initial_freq_khz = cfg.host_clk_freq_khz;
    int freq_delta = int'(host_target_freq_khz) - initial_freq_khz;
    // Total cycle count over which to drift; half the expected test duration to leave intervals
    // at the start (set up) and the end (hopefully 'synchronized' and transfers are successful).
    uint total_cycles = CYCLES_PER_FRAME * num_frames / 2;
    uint elapsed_cycles = 0;
    `uvm_info(`gfn, $sformatf("Driving the host clk from %dkHz to %dkHz",
                              initial_freq_khz, host_target_freq_khz), UVM_MEDIUM)

    while (!all_frames_done && elapsed_cycles < total_cycles) begin
      // Decide how many clocks to wait before applying a correction; we must keep this small to
      // avoid significant step changes in the frequency since they may be expected to produce
      // transmission errors.
      uint wait_cycles = $urandom_range(512, 1024);
      if (wait_cycles > total_cycles - elapsed_cycles) wait_cycles = total_cycles - elapsed_cycles;
      cfg.host_clk_rst_vif.wait_clks(wait_cycles);
      elapsed_cycles += wait_cycles;
      set_host_clk(initial_freq_khz + (freq_delta * int'(elapsed_cycles)) / int'(total_cycles));
    end
  endtask

  // Parallel task generates SOF periodically, dividing the bus activity into discrete
  // bus frames and indicating when transmission of regular bus traffic may occur.
  virtual task bus_framing();
    // Whatever the actual host frequency, we want to generate a SOF every 48_000 clock
    // cycles, since this equates to 1ms in the host's time frame.
    int unsigned elapsed_cycles = 0;
    while (!all_frames_done) begin
      cfg.host_clk_rst_vif.wait_clks(48_000 - elapsed_cycles);
      elapsed_cycles = 0;
      fork
        begin : isolation_fork
          fork
            while (1) begin
              cfg.host_clk_rst_vif.wait_clks(1);
              elapsed_cycles++;
            end
            begin
              // Use the 'worst possible' frame number to generate a maximal length SOF packet;
              //  (this is one of a handful of frame numbers that require two bit stuffed zeros,
              //   experimentally determined).
              send_sof_packet(PidTypeSofToken, 11'h7fe);
              can_transmit = 1;
              // Track the number of SOF packets sent, so that the end of the 'reset recovery'
              // period can be detected.
              sof_sent++;
              if (sof_sent >= 10) reset_recovery = 0;
            end
          join_any
          disable fork;
        end : isolation_fork
      join
    end
  endtask

  // Await (with timeout) the next USB timing reference pulse from the DUT; this shall be pulsed
  // every 1ms indicating detection of a Start Of Frame packet from the USB host controller.
  virtual task wait_ref_pulse();
    fork
      begin : isolation_fork
        fork
          begin
            // DUT will declare 'host lost' after just 4 bus frames; we'll wait a little longer
            // before giving up ourselves in case it recovers.
            cfg.clk_rst_vif.wait_clks(5 * CYCLES_PER_FRAME);
            `uvm_fatal(`gfn, "No usb_ref_pulse_i assertion; host lost")
          end
          @(posedge cfg.osc_tuning_vif.usb_ref_pulse_i);
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  // Parallel task receives reference pulses indicating the reception of SOF packets
  // and allowing the DUT oscillator to be tuned to match that of the USB host.
  virtual task sof_tracking();
    // Clock period in picoseconds for a 48MHz oscillator.
    localparam int CYCLE_PS = 1_000_000 / 48;
    // The most recent delta measurements
    localparam int unsigned NDELTAS = 8;
    int deltas[NDELTAS];
    int idx = 0;

    while (!all_frames_done) begin
      int total_delta = 0;
      int mean_delta_ps;
      int elapsed_cycles;

      wait_ref_pulse();
      elapsed_cycles = cfg.osc_tuning_vif.elapsed_dut_cycles();

      // Update the sliding window of delta measurements; we're using a simple weighted average
      // to provide some robustness whilst tracking a potentially-varying host clock, but we're not
      // trying to model a realistic variable frequency oscillator too closely.
      //
      // The aim is just to achieve convergence upon a static target frequency within a reasonable
      // number of bus frames. The USB host must guarantee 10ms of post-Bus Reset recovery during
      // which only SOF packets are transmitted to the DUT, equivalent to 10 bus frames.

      // A positive cycle delta indicates that the DUT is running faster than the host and its
      // oscillator should be slowed. A negative cycle delta indicates the opposite.
      elapsed_cycles -= CYCLES_PER_FRAME;
      `uvm_info(`gfn, $sformatf("Bus frame was measured as %d cycles", elapsed_cycles), UVM_HIGH)
      deltas[idx] = elapsed_cycles;
      begin
        int unsigned i = idx;
        int n = 1;
        do begin
          total_delta += deltas[i] / n;
          `uvm_info(`gfn, $sformatf("total_delta becoming %d adding %d/%d", total_delta,
                                    deltas[i], n), UVM_HIGH)
          i = ((i >= NDELTAS - 1) ? 0 : (i + 1));
          n = n * 2;  // limit(sum(1/2^n)) for n >= 0 is 2.
        end while (i != idx);
      end
      idx = ((idx > 0) ? idx : NDELTAS) - 1;

      // Convert the average cycle difference to an adjustment in picoseconds, using a clock
      // frequency of 48MHz; if our cycle count is too high, we need to lengthen the clock period.
      mean_delta_ps = (total_delta * CYCLE_PS) / 2;  // Div 2 corrects for weighted sum.

      // The mean delta in picoseconds must be amortized over all of the bits in the bus frame.
      adjust_usb_clk(mean_delta_ps / CYCLES_PER_FRAME);
    end
  endtask

  // Transmission of packet data
  virtual task bus_traffic();
    repeat (num_frames) begin
      // Prevent collision between DATA packets and SOF packet at frame start.
      while (!can_transmit) begin
        cfg.host_clk_rst_vif.wait_clks(8);
      end
      can_transmit = 0;
      // Transmit enough packets to fill about 2/3 of the bus frame.
      if (with_traffic & !reset_recovery & !sof_only) transmit_out_packets(10);
    end
    // Signal to the other processes that all test frames have been completed and they should stop.
    all_frames_done = 1;
  endtask

  virtual task pre_start();
    // Vary the initial DUT clock frequency in these test sequences.
    if ($value$plusargs("usb_freq_delta=%0d", usb_freq_delta)) begin
      cfg.usb_clk_freq_khz = 48_000 + (usb_freq_delta + 500) / 1000;  // round to nearest
    end else begin
      // The DUT frequency is kept constant by default in other vseqs, but we want to randomize it
      // too for freq/phase testing, not just that of the host.
      cfg.usb_clk_freq_khz = $urandom_range(USB_CLK_FREQ_MIN_KHZ, USB_CLK_FREQ_MAX_KHZ);
    end
    // Vary the initial host clock frequency, or let the base class randomize it.
    if ($value$plusargs("host_freq_delta=%0d", host_freq_delta)) begin
      cfg.host_clk_freq_khz = 48_000 + (host_freq_delta + 500) / 1000;  // round to nearest
    end

    // Testpoint settings to control the behavior of this sequence.
    void'($value$plusargs("host_drifting=%d",  host_drifting));  // Host clk a moving target.
    void'($value$plusargs("osc_tracking=%d",   osc_tracking));   // DUT clk must track host clk.
    void'($value$plusargs("with_traffic=%d",   with_traffic));   // Transmit OUT DATA traffic.
    void'($value$plusargs("reset_recovery=%d", reset_recovery)); // Observe Reset Recovery?
    void'($value$plusargs("sof_only=%d",       sof_only));       // Diagnostic/development aid.

    super.pre_start();
  endtask

  virtual task body();
    // Report test configuration.
    `uvm_info(`gfn, $sformatf("usb_freq_delta  %0d", usb_freq_delta),  UVM_LOW)
    `uvm_info(`gfn, $sformatf("host_freq_delta %0d", host_freq_delta), UVM_LOW)
    `uvm_info(`gfn, $sformatf("host_drifting   %0d", host_drifting),   UVM_LOW)
    `uvm_info(`gfn, $sformatf("osc_tracking    %0d", osc_tracking),    UVM_LOW)
    `uvm_info(`gfn, $sformatf("with_traffic    %0d", with_traffic),    UVM_LOW)
    `uvm_info(`gfn, $sformatf("reset_recovery  %0d", reset_recovery),  UVM_LOW)
    `uvm_info(`gfn, $sformatf("sof_only        %0d", sof_only),        UVM_LOW)

    configure_out_trans(ep_default);

    // Do not proceed further until the device has exited the Bus Reset signaling of the
    // usb20_driver module.
    wait_for_link_state({LinkActive, LinkActiveNoSOF}, 10 * 1000 * 48);  // 10ms timeout, at 48MHz

    // Initialize test state.
    sof_sent = 0;
    can_transmit = 0;
    all_frames_done = 0;

    fork
      if (host_drifting) host_drift();
      // Periodic generation of SOF packets by the USB host.
      bus_framing();
      // Tracking of bus frames and adjustment of DUT clock frequency.
      if (osc_tracking) sof_tracking();
      // Generation of bus traffic, and control of test completion.
      bus_traffic();
    join
  endtask

endclass : usbdev_freq_phase_delta_vseq
