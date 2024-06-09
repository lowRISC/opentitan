// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Issue randomized bus-level events (Bus Resets, Suspend-Resume Signaling and/or VBUS
// disconnections)  during a streaming test. Note that when such a stimulus is produced we do not
// really expect the current traffic to be unaffected, since the DUT would normally be reconfigured
// by the USB host upon reconnection.
//
// Rather, the aim is to test the DUT does not get stuck in an irrecoverable state preventing
// communications from being re-established. The host- and device-side code in
// `usbdev_max_usb_traffic_vseq` is thus notified of Bus Resets event, so that it can adapt its
// internal state according to the expect DUT changes. (eg. zeroing of device address and resetting
// of data toggles.)

class usbdev_bus_rand_vseq extends usbdev_max_usb_traffic_vseq;
  `uvm_object_utils(usbdev_bus_rand_vseq)

  `uvm_object_new

  // Min/max duration of Resume Signaling, in microseconds.
  //
  // Note: We cannot shorten the duration of /Suspend/ Signaling (> 3ms) because this is fixed by
  // the design of the RTL presently. The DUT will not enter a Suspended state until over 3ms of
  // Idle state has been detected.
  int unsigned min_resume_duration = 100;
  int unsigned max_resume_duration = 1000;

  // Min/max duration of Bus Resets, in microseconds.
  int unsigned min_reset_duration = 10;
  int unsigned max_reset_duration = 1000;

  // Min/max duration of VBUS Disconnections, in microseconds.
  int unsigned min_disconnect_duration = 10;
  int unsigned max_disconnect_duration = 100;

  // Generate a Bus Reset during streaming.
  //
  // Note: Bus Resets from a real host would be more than 10ms, but we typically employ a shorter
  // delay to avoid wasting simulation time.
  task generate_bus_reset();
    int unsigned reset_duration_usecs;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(reset_duration_usecs,
                                       reset_duration_usecs >= min_reset_duration;
                                       reset_duration_usecs <= max_reset_duration;)
    `uvm_info(`gfn, "Performing Bus Reset", UVM_MEDIUM)
    send_bus_reset(reset_duration_usecs);
  endtask

  // Generate a VBUS Disconnection during streaming.
  task generate_vbus_disconnect();
    int unsigned disconn_duration_usecs;
    int unsigned reset_duration_usecs;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(disconn_duration_usecs,
                                       disconn_duration_usecs >= min_disconnect_duration;
                                       disconn_duration_usecs <= max_disconnect_duration;)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(reset_duration_usecs,
                                       reset_duration_usecs >= min_reset_duration;
                                       reset_duration_usecs <= max_reset_duration;)
    `uvm_info(`gfn, $sformatf("Disconnecting VBUS for %d usecs and resetting for %d usecs",
                              disconn_duration_usecs, reset_duration_usecs),
              UVM_MEDIUM)
    vbus_disconnect(disconn_duration_usecs, reset_duration_usecs);
  endtask

  // Generate Suspend-Resume Signaling during streaming.
  //
  // Note: Resume Signaling from a real host would be more than 20ms, but we employ a shorter
  // delay to avoid wasting simulation time.
  task generate_suspend_resume();
    int unsigned resume_duration_usecs;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(resume_duration_usecs,
                                       resume_duration_usecs >= min_resume_duration;
                                       resume_duration_usecs <= max_resume_duration;)
    suspend_resume(resume_duration_usecs);
  endtask

  // Parallel process that randomly generates bus events.
  // - Suspend-Resume Signaling.
  // - Bus Resets.
  // - VBUS Disconnections.
  task generate_bus_events();
    // The set of events from which we may choose.
    bit [2:0] event_mask = {do_resume_signaling, do_reset_signaling, do_vbus_disconnects};

    // Report the bus events that we shall generate, and collect the min/max durations if specified
    // in the test point.
    if (do_resume_signaling) begin
      `uvm_info(`gfn, "Performing Suspend-Resume Signaling during sequence", UVM_LOW)
      void'($value$plusargs("min_resume_duration=%d", min_resume_duration));
      void'($value$plusargs("max_resume_duration=%d", max_resume_duration));
    end
    if (do_reset_signaling) begin
      `uvm_info(`gfn, "Performing Bus Resets during sequence", UVM_LOW)
      void'($value$plusargs("min_reset_duration=%d", min_reset_duration));
      void'($value$plusargs("max_reset_duration=%d", max_reset_duration));
    end
    if (do_vbus_disconnects) begin
      `uvm_info(`gfn, "Performing VBUS Disconnections during sequence", UVM_LOW)
      void'($value$plusargs("min_disconnect_duration=%d", min_disconnect_duration));
      void'($value$plusargs("max_disconnect_duration=%d", max_disconnect_duration));
    end

    // Generate bus events randomly until asked to stop.
    while (event_mask && !traffic_stop) begin
      bit [17:0] event_delay;
      bit [2:0] event_type;
      `DV_CHECK_STD_RANDOMIZE_FATAL(event_delay)
      fork
        begin : isolation_fork
          fork
            cfg.clk_rst_vif.wait_clks(event_delay);
            wait (traffic_stop);
          join_any
          disable fork;
        end : isolation_fork
      join
      // TODO: some kind of arbitration for equal priority would be beneficial here.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(event_type, (event_type & event_mask) != 0;)
      casez (event_type)
        3'b1??:  generate_suspend_resume();
        3'b01?:  generate_bus_reset();
        default: generate_vbus_disconnect();
      endcase
    end
  endtask

  virtual task body;
    // `usbdev_base_vseq` collects the overall bus-level configuration to be used.
    `uvm_info(`gfn, $sformatf("do_resume_signaling %d", do_resume_signaling), UVM_LOW)
    `uvm_info(`gfn, $sformatf("do_reset_signaling  %d", do_reset_signaling),  UVM_LOW)
    `uvm_info(`gfn, $sformatf("do_vbus_disconnects %d", do_vbus_disconnects), UVM_LOW)
    fork
      super.body();
      generate_bus_events();
    join
  endtask
endclass : usbdev_bus_rand_vseq
