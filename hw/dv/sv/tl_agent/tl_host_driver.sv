// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A TileLink driver that behaves as a host, initiating TileLink transactions
class tl_host_driver extends tl_base_driver;
  `uvm_component_utils(tl_host_driver)

  // A queue of sequence items corresponding to the requests have been sent on the A channel but
  // haven't yet had a response on the D channel.
  protected tl_seq_item pending_a_req[$];

  // A flag that is true whenever reset is asserted on the bus. This is maintained by the
  // reset_signals task.
  protected bit reset_asserted;

  extern function new (string name="", uvm_component parent=null);

  // Drive items received from the sequencer. This implements a task declared in dv_base_driver.
  extern task get_and_drive();

  // Clear output signals and internal state whenever a reset happens. This task runs forever,
  // looping over resets.
  //
  // This also controls an internal reset_asserted flag, which is used by other tasks in the class
  // to detect resets. This implements a task declared in dv_base_driver.
  extern task reset_signals();

  // Wait for the next edge of host_cb. Stops early if reset is asserted.
  extern protected task wait_clk_or_rst();

  // Get items from the sequencer and drive them on the A channel. This runs forever and runs
  // synchronised with the TL clock.
  //
  // If we go into reset, this will flush all pending items from the sequencer, and continue
  // flushing items until reset is deasserted.
  extern protected task a_channel_thread();

  // Send a request, req, on the A channel
  extern protected task send_a_channel_request(tl_seq_item req);

  // Send the body of a request on the A channel.
  //
  // req:            The request whose body should be sent.
  //
  // a_valid_len:    The number of host clock cycles a_valid is held high waiting for a_ready to go
  //                 high and accept the request. If req has req_abort_after_a_valid_len set, or if
  //                 the cfg has allow_a_valid_drop_wo_a_ready, then the driver will drop a_valid
  //                 again after that time, write 'x values to the A channel and exit.
  //
  // req_done [out]  This is set to 1'b1 if a_ready has gone high on the host clock.
  //
  // req_abort [out] This is set to 1'b1 if the host decides to drop a_valid because the receiever
  //                 hasn't responded with a_ready.
  extern protected task send_a_request_body(tl_seq_item req, int a_valid_len,
                                            output bit req_done, output bit req_abort);

  // Drive the d_ready pin (as the host) forever to allow a device to send responses back
  //
  // This waits a random number of host clock cycles (between cfg.d_ready_delay_min and
  // cfg.d_ready_delay_max) and then pulses d_ready high for a cycle before dropping again.
  //
  // If cfg.host_can_stall_rsp_when_a_valid_high is false then the driver setting a_valid high will
  // cause this task to skip any wait period with d_ready low and hold it high.
  extern protected task d_ready_rsp();

  // Collect responses on the D channel
  //
  // A response is signalled by the device setting d_valid when we (the host) have set d_ready. The
  // request to which this is a response is found by searching for d_source in the queue of pending
  // requests.
  //
  // When a match is found, this task puts a response to seq_item_port (sending it back to the
  // sequencer), then deletes the pending request.
  //
  // If the internal reset_asserted flag is high, this task responds to all pending requests (with
  // potentially silly data values)
  extern protected task d_channel_thread();

  // Return true if the given source is the a_source value of some pending request.
  extern protected function bit is_source_in_pending_req(bit [SourceWidth-1:0] source);

  // Write rubbish to the A channel to invalidate it and set a_valid to zero
  //
  // If cfg.invalidate_a_x is true then all fields other than a_valid will be set to 'x. If it is
  // false then all the fields will be randomised.
  extern protected function void invalidate_a_channel();
endclass : tl_host_driver

function tl_host_driver::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction

task tl_host_driver::get_and_drive();
  // Wait for initial reset to pass.
  wait(cfg.vif.rst_n === 1'b1);
  @(cfg.vif.host_cb);
  fork
    a_channel_thread();
    d_channel_thread();
    d_ready_rsp();
  join_none
endtask

task tl_host_driver::reset_signals();
  reset_asserted = (cfg.vif.rst_n === 1'b0);
  forever begin
    // At the start of the loop body, we should either be at the start of the simulation or have
    // just entered reset. Invalidate all signals and mark ourselves as not ready on the D channel.
    invalidate_a_channel();
    cfg.vif.h2d_int.d_ready <= 1'b0;

    // Now wait to come out of reset then clear the reset_asserted signal. (Note that if the
    // simulation started not in reset then this first wait will take zero time).
    wait(cfg.vif.rst_n);
    reset_asserted = 1'b0;

    // When we were in reset, we should have flushed all sequence items immediately. To check this
    // has worked correctly, the following things should be true when we leave reset:
    //
    //  - The pending_a_req queue should be empty (d_channel_thread should have sent responses and
    //    flushed the requests).
    //
    //  - The sequencer shouldn't have any items available through seq_item_port. If an item had
    //    been available, we should have taken it immediately in get_and_drive.
    `DV_CHECK_EQ(pending_a_req.size(), 0)
    `DV_CHECK_EQ(seq_item_port.has_do_available(), 0)

    // At this point, we're in the main part of the simulation and the get_and_drive task will be
    // driving sequence items over the bus. Wait until reset is asserted then set the reset_asserted
    // signal again.
    wait(!cfg.vif.rst_n);
    reset_asserted = 1'b1;
  end
endtask

task tl_host_driver::wait_clk_or_rst();
  `DV_SPINWAIT_EXIT(@(cfg.vif.host_cb);, wait(reset_asserted);)
endtask

task tl_host_driver::a_channel_thread();
  // Each time the body of the main loop of a_channel_thread, we expect either to be synchronised
  // with the TL clock or to be in reset. Make sure that is true from the start of the task.
  wait_clk_or_rst();

  forever begin
    // Grab as many items as we can from seq_item_port and immediately send them on the bus. The
    // calls to try_next_item will not block, but sending the items on the bus probably will (unless
    // we enter reset).
    forever begin
      seq_item_port.try_next_item(req);
      if (req == null) break;
      send_a_channel_request(req);
    end

    // We just looked and seq_item_port didn't have an item. Wait a clock before we try again, but
    // stop waiting if we happen to enter reset.
    wait_clk_or_rst();

    // If we are not in reset, we've just waited the cycle we wanted to wait and we should go back
    // to the start of the loop and try again.
    if (!reset_asserted) continue;

    // If we get here, we *are* in reset and we should switch to a different mode where we
    // continuously flush seq_item_port.
    forever begin
      // Wait for the next item, but drop out early if we leave reset
      `DV_SPINWAIT_EXIT(seq_item_port.get_next_item(req);,
                        wait(!reset_asserted);)
      if (!reset_asserted) break;

      // If we get here then we are still in reset and the get_next_item() call yielded an item in
      // req. Send the A-channel request (which will complete in zero time)
      send_a_channel_request(req);
    end

    // At this point, we've just come out of reset. Resynchronise to the TL clock before we go
    // around the loop again. If we go into reset again before the clock edge, we'll go back to the
    // top of the loop, but nothing will consume time until we get back to the forever loop we've
    // just finished.
    wait_clk_or_rst();
  end
endtask

task tl_host_driver::send_a_channel_request(tl_seq_item req);
  int unsigned a_valid_delay, a_valid_len;
  bit req_done = 1'b0, req_abort = 1'b0;

  // Seq may override the a_source or all valid sources are used but still send req, in which case
  // it is possible that it might not have factored
  // This wait is only needed in xbar test as xbar can use all valid sources and xbar_stress runs
  // all seq in parallel, which needs driver to stall when the source is currently being used
  // in the a_source values from pending requests that have not yet completed. If that is true, we
  // need to insert additional delays to ensure we do not end up sending the new request whose
  // a_source matches one of the pending requests.
  `DV_SPINWAIT_EXIT(while (is_source_in_pending_req(req.a_source)) @(cfg.vif.host_cb);,
                    wait(reset_asserted);)

  while (!req_done && !req_abort && !reset_asserted) begin
    if (cfg.use_seq_item_a_valid_delay) begin
      a_valid_delay = req.a_valid_delay;
    end else begin
      a_valid_delay = $urandom_range(cfg.a_valid_delay_min, cfg.a_valid_delay_max);
    end

    if (req.req_abort_after_a_valid_len || cfg.allow_a_valid_drop_wo_a_ready) begin
      if (cfg.use_seq_item_a_valid_len) begin
        a_valid_len = req.a_valid_len;
      end else begin
        a_valid_len = $urandom_range(cfg.a_valid_len_min, cfg.a_valid_len_max);
      end
    end

    // break delay loop if reset asserted to release blocking
    `DV_SPINWAIT_EXIT(repeat (a_valid_delay) @(cfg.vif.host_cb);,
                      wait(reset_asserted);)

    if (!reset_asserted) begin
      pending_a_req.push_back(req);
      cfg.vif.host_cb.h2d_int.a_address <= req.a_addr;
      cfg.vif.host_cb.h2d_int.a_opcode  <= tl_a_op_e'(req.a_opcode);
      cfg.vif.host_cb.h2d_int.a_size    <= req.a_size;
      cfg.vif.host_cb.h2d_int.a_param   <= req.a_param;
      cfg.vif.host_cb.h2d_int.a_data    <= req.a_data;
      cfg.vif.host_cb.h2d_int.a_mask    <= req.a_mask;
      cfg.vif.host_cb.h2d_int.a_user    <= req.a_user;
      cfg.vif.host_cb.h2d_int.a_source  <= req.a_source;
      cfg.vif.host_cb.h2d_int.a_valid   <= 1'b1;
    end else begin
      req_abort = 1;
    end
    // drop valid if it lasts for a_valid_len, even there is no a_ready
    `DV_SPINWAIT_EXIT(send_a_request_body(req, a_valid_len, req_done, req_abort);,
                      wait(reset_asserted);)

    // when reset and host_cb.h2d_int.a_valid <= 1 occur at the same time, if clock is off,
    // there is a race condition and invalidate_a_channel can't clear a_valid.
    if (reset_asserted) cfg.vif.host_cb.h2d_int.a_valid <= 1'b0;
    invalidate_a_channel();
  end
  seq_item_port.item_done();
  if (req_abort || reset_asserted) begin
    req.req_completed = 0;
    // Just wire the d_source back to a_source to avoid errors in upstream logic.
    req.d_source = req.a_source;
    seq_item_port.put_response(req);
  end else begin
    req.req_completed = 1;
  end
  `uvm_info(get_full_name(), $sformatf("Req %0s: %0s", req_abort ? "aborted" : "sent",
                                       req.convert2string()), UVM_HIGH)
endtask

task tl_host_driver::send_a_request_body(tl_seq_item req, int a_valid_len,
                                         output bit req_done, output bit req_abort);
  int unsigned a_valid_cnt = 0;
  req_done = 1'b0;
  req_abort = 1'b0;

  while (1) begin
    @(cfg.vif.host_cb);
    a_valid_cnt++;
    if (cfg.vif.host_cb.d2h.a_ready) begin
      req_done = 1;
      break;
    end else if ((req.req_abort_after_a_valid_len || cfg.allow_a_valid_drop_wo_a_ready) &&
                 a_valid_cnt >= a_valid_len) begin
      if (req.req_abort_after_a_valid_len) req_abort = 1;
      cfg.vif.host_cb.h2d_int.a_valid <= 1'b0;
      // remove unaccepted item
      void'(pending_a_req.pop_back());
      invalidate_a_channel();
      @(cfg.vif.host_cb);
      break;
    end
  end
endtask

task tl_host_driver::d_ready_rsp();
  int unsigned d_ready_delay;
  tl_seq_item rsp;

  forever begin
    bit req_found;
    d_ready_delay = $urandom_range(cfg.d_ready_delay_min, cfg.d_ready_delay_max);
    // if a_valid high then d_ready must be high, exit the delay when a_valid is set
    repeat (d_ready_delay) begin
      if (!cfg.host_can_stall_rsp_when_a_valid_high && cfg.vif.h2d_int.a_valid) break;
      @(cfg.vif.host_cb);
    end

    cfg.vif.host_cb.h2d_int.d_ready <= 1'b1;
    @(cfg.vif.host_cb);
    cfg.vif.host_cb.h2d_int.d_ready <= 1'b0;
  end
endtask

task tl_host_driver::d_channel_thread();
  int unsigned d_ready_delay;
  tl_seq_item rsp;

  forever begin
    if ((cfg.vif.host_cb.d2h.d_valid && cfg.vif.h2d_int.d_ready && !reset_asserted) ||
        ((pending_a_req.size() != 0) & reset_asserted)) begin
      // Use the source ID to find the matching request
      foreach (pending_a_req[i]) begin
        if ((pending_a_req[i].a_source == cfg.vif.host_cb.d2h.d_source) | reset_asserted) begin
          rsp = pending_a_req[i];
          rsp.d_opcode = cfg.vif.host_cb.d2h.d_opcode;
          rsp.d_data   = cfg.vif.host_cb.d2h.d_data;
          rsp.d_param  = cfg.vif.host_cb.d2h.d_param;
          rsp.d_sink   = cfg.vif.host_cb.d2h.d_sink;
          rsp.d_size   = cfg.vif.host_cb.d2h.d_size;
          rsp.d_user   = cfg.vif.host_cb.d2h.d_user;
          // set d_error = 0 and rsp_completed = 0 when reset occurs
          rsp.d_error  = reset_asserted ? 0 : cfg.vif.host_cb.d2h.d_error;
          // make sure every req has a rsp with same source even during reset
          if (reset_asserted) rsp.d_source = rsp.a_source;
          else                rsp.d_source = cfg.vif.host_cb.d2h.d_source;
          seq_item_port.put_response(rsp);
          pending_a_req.delete(i);
          `uvm_info(get_full_name(), $sformatf("Got response %0s, pending req:%0d",
                                     rsp.convert2string(), pending_a_req.size()), UVM_HIGH)
          rsp.rsp_completed = !reset_asserted;
          break;
        end
      end

      // If there was a matching request, we responded to it above. If not, the device seems to
      // have sent a response without a request (and we won't have done anything yet).
      //
      // If we're in reset, we might have forgotten the request (and can ignore the response). If
      // not, we wouldn't normally expect this to happen. This is a property that is checked in
      // the tlul_assert module, which should be bound in. But it *might* happen if we're doing
      // fault injection and disabling assertions in that module.
      //
      // Ignore the response either way: we're a driver and there is definitely no sequence that
      // is waiting for the response here. If there's a bug in the design and we're generating
      // spurious responses, we expect something to fail in tlul_assert.
    end else if (reset_asserted) begin
      wait(!reset_asserted);
    end
    wait_clk_or_rst();
  end
endtask

function bit tl_host_driver::is_source_in_pending_req(bit [SourceWidth-1:0] source);
  foreach (pending_a_req[i]) begin
    if (pending_a_req[i].a_source == source) return 1;
  end
  return 0;
endfunction

function void tl_host_driver::invalidate_a_channel();
  if (cfg.invalidate_a_x) begin
    cfg.vif.h2d_int.a_opcode <= tlul_pkg::tl_a_op_e'('x);
    cfg.vif.h2d_int.a_param <= '{default:'x};
    cfg.vif.h2d_int.a_size <= '{default:'x};
    cfg.vif.h2d_int.a_source <= '{default:'x};
    cfg.vif.h2d_int.a_address <= '{default:'x};
    cfg.vif.h2d_int.a_mask <= '{default:'x};
    cfg.vif.h2d_int.a_data <= '{default:'x};
    // The assignment to instr_type must have a cast since the LRM doesn't allow enum assignment of
    // values not belonging to the enumeration set.
    cfg.vif.h2d_int.a_user <= '{instr_type:prim_mubi_pkg::mubi4_t'('x), default:'x};
    cfg.vif.h2d_int.a_valid <= 1'b0;
  end else begin
    tlul_pkg::tl_h2d_t h2d;
    `DV_CHECK_STD_RANDOMIZE_FATAL(h2d)
    h2d.a_valid = 1'b0;
    cfg.vif.h2d_int <= h2d;
  end
endfunction
