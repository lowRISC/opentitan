// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that behaves as an alert_receiver. This is used in alert_esc_agent when configured in
// "device mode"

class alert_receiver_driver extends alert_base_driver;
  `uvm_component_utils(alert_receiver_driver)

  // The drive_req_between_resets task will consume requests from m_requests and add these requests
  // to this pair of FIFOs (to be consumed by the send_pings and send_alert_rsps tasks that it
  // spawns).
  //
  // When reset is asserted, both of those tasks will exit after flushing their respective queues.
  local uvm_tlm_analysis_fifo #(alert_seq_item) m_pending_pings;
  local uvm_tlm_analysis_fifo #(alert_seq_item) m_pending_alert_rsps;

  // When a ping gets an alert response or a genuine alert is sent, this driver needs to acknowledge
  // the alert, but the two options need to be handled serially. The ack is handled by ack_alert,
  // which uses this semaphore as a mutex.
  local semaphore m_ack_semaphore;

  extern function new(string name, uvm_component parent);

  // Clear interface signals because reset has been asserted
  //
  // This implements a task in dv_base_driver
  extern task on_enter_reset();

  // Drive requests that have been seen by alert_base_driver::get_req. This task runs forever.
  //
  // This implements a task in alert_base_driver
  extern task drive_req();

  // Take items from m_requests and (depending on the type of the item) add them to m_pending_pings
  // and m_pending_alert_rsps.
  //
  // Exits immediately on reset.
  extern local task consume_requests_betwen_resets();

  // Drive requests that have been seen by alert_base_driver::get_req, until the next reset. This is
  // called by drive_req.
  extern local task drive_req_between_resets();

  // Drive any items that were added to m_pending_pings.
  //
  // Exits early on reset.
  extern local task send_pings();

  // Drive any items that were added to m_pending_alert_rsps.
  //
  // Exits early on reset.
  extern local task send_alert_rsps();

  // Send a ping described by item.
  //
  // Exits early on reset.
  extern local task send_ping(alert_seq_item item);

  // Handle a sequence item that demands an alert response
  //
  // An item should only be added to that queue in response to an alert being generated on the
  // interface. We will wait a randomised time (in ack_alert) before acknowledging the alert.
  //
  // Exits early on reset.
  extern local task send_alert_rsp(alert_seq_item item);

  // Wait for a short time to allow an alert to propagate through the clocking blocks in the
  // interface. The max_cycles argument is the maximum number of cycles to wait.
  //
  // The task will stop as soon as any of these events happens:
  //
  //    - The alert_p signal goes high in receiver_cb.
  //    - There have been max_cycles edges of both clocks.
  //    - A reset is asserted.
  extern local task wait_for_alert_propagation(int unsigned max_cycles);

  // Drive an alert ping
  //
  // This will start by waiting ping_delay cycles before sending the ping request. Once the ping has
  // gone out, we wait for an alert to arrive and then acknowledge it using ack_alert (and
  // passing ack_delay and ack_stable).
  //
  // The task allows to retract driving the ping. If there's an alert (r_alert_rsp_q.size > 0)
  // before the 'ping_delay' the ping is aborted and the driver moves to tackle the alert in
  // 'rsp_alert' task. This is notified by setting `item_not_driven=1`
  //
  // The task exits early on reset.
  extern local task drive_alert_ping(int unsigned ping_delay,
                                     int unsigned ack_delay,
                                     int unsigned ack_stable);

  // Acknowledge the next alert
  //
  // This task waits until an alert is signalled, then waits a short time before acknowledging the
  // alert. Once the ack has been asserted, the ack stays high for a time before it, in turn, drops.
  //
  // This task uses m_ack_semaphore as a mutex (to serialise ping response acks and other alert
  // acks).
  //
  // The delay before the initial ack is normally randomised in the range [cfg.ack_delay_min,
  // cfg.ack_delay_max] cycles. If cfg.use_seq_item_ack_delay is true then the delay is from the
  // ack_delay argument.
  //
  // Similarly, the ack stays in place for a time that is normally randomised in the range
  // [cfg.ack_stable_min, cfg.ack_stable_max]. If cfg.use_seq_item_ack_stable is true then the ack
  // stays stable for the number of cycles in the ack_stable argument.
  //
  // Both of these times will be truncated if cfg.fast_rcvr is true. In that case, they will be
  // cfg.ack_delay_min, cfg.ack_stable_min respectively.
  //
  // The task will exit quickly on reset (replacing the token on the semaphore)
  extern local task ack_alert(int unsigned ack_delay, int unsigned ack_stable);

  // Set the ack signal to be the given boolean value (so either 0;1 or 1;0)
  extern local task set_ack(bit asserted);

  // Toggle the ping state
  extern local task set_ping();

  // Set the ping state to 0;1 (the reset value)
  extern task reset_ping();

  // Perform the alert init handshake, exiting early on reset
  extern task do_alert_rx_init();

  // Wait for num_cycles positive edges of the slower of the two clocks
  //
  // Return early on reset.
  extern task wait_slower_clock(int unsigned num_cycles);
endclass : alert_receiver_driver

function alert_receiver_driver::new(string name, uvm_component parent);
  super.new(name, parent);
  m_ack_semaphore = new(1);
  m_pending_pings = new("m_pending_pings", this);
  m_pending_alert_rsps = new("m_pending_alert_rsps", this);
endfunction

task alert_receiver_driver::on_enter_reset();
  // Clear ping and ack signals (both the actual signals and the clocking block values)
  cfg.vif.alert_rx_int.ping_p <= 1'b0;
  cfg.vif.alert_rx_int.ping_n <= 1'b1;
  cfg.vif.alert_rx_int.ack_p <= 1'b0;
  cfg.vif.alert_rx_int.ack_n <= 1'b1;
  cfg.vif.receiver_cb.alert_rx_int.ping_p <= 1'b0;
  cfg.vif.receiver_cb.alert_rx_int.ping_n <= 1'b1;
  cfg.vif.receiver_cb.alert_rx_int.ack_p <= 1'b0;
  cfg.vif.receiver_cb.alert_rx_int.ack_n <= 1'b1;
endtask

task alert_receiver_driver::drive_req();
  forever begin
    // Wait until we are out of reset. Until that happens, respond instantly to any sequence items
    // that come in.
    while (cfg.in_reset) begin
      fork : isolation_fork begin
        alert_seq_item item;
        fork
          wait (!cfg.in_reset);
          m_requests.get(item);
        join_any
        disable fork;
        // Since we are in reset, we ignore any item that we see. Because it was fetched by get() in
        // alert_base_driver (instead of with get_next_item()), we do not have to declare it done.
      end join
    end

    drive_req_between_resets();
  end
endtask

task alert_receiver_driver::consume_requests_betwen_resets();
  fork : isolation_fork begin
    fork
      wait (cfg.in_reset);
      forever begin
        alert_seq_item item;
        m_requests.get(item);

        case (item.m_txn_type)
          alert_seq_item::AlertTxn: m_pending_alert_rsps.write(item);
          alert_seq_item::PingTxn:  m_pending_pings.write(item);
          default: `uvm_fatal(get_full_name(), "Unknown txn type")
        endcase
      end
    join_any
    disable fork;
  end join
endtask

task alert_receiver_driver::drive_req_between_resets();
  // Drive the init protocol from the receiver side. do_alert_rx_init will exit early if it sees
  // reset.
  do_alert_rx_init();
  if (cfg.in_reset) return;

  // Fetch items to drive and drive them. The first task takes items from the m_requests fifo and
  // uses them to populate m_pending_pings and m_pending_alert_rsps. The second two tasks take (and
  // drive) items from those two fifos.
  //
  // All three tasks exit on reset.
  fork
    consume_requests_betwen_resets();
    send_alert_rsps();
    send_pings();
  join

  // As a consistency check, make sure that m_pending_pings and m_pending_alert_rsps were cleared by
  // send_alert_rsps and send_pings before they exited.
  if (m_pending_pings.size())
    `uvm_error(get_full_name(),
               $sformatf("m_pending_pings nonempty after reset: %0p", m_pending_pings))
  if (m_pending_alert_rsps.size())
    `uvm_error(get_full_name(),
               $sformatf("m_pending_alert_rsps nonempty after reset: %0p", m_pending_alert_rsps))
endtask

task alert_receiver_driver::send_pings();
  alert_seq_item item;

  while(!cfg.in_reset) begin
    // Clear the item variable (so that we can tell whether the fork below gets an item or sees a
    // reset)
    item = null;

    fork : isolation_fork begin
      fork
        wait (cfg.in_reset);
        m_pending_pings.get(item);
      join_any
      disable fork;
    end join

    // If there is an item, send it with send_ping. The task will exit early on reset.
    if (item != null) begin
      send_ping(item);

      // Now that the item has been sent, report this to the sequencer
      seq_item_port.put_response(item);
    end
  end

  // When we get here, we must be in reset. m_pending_pings might be nonempty (if reset was asserted
  // when there were lots of pending pings). Report all the items done (in a trivial way) before
  // returning.
  while(m_pending_pings.try_get(item)) seq_item_port.put_response(item);
endtask

task alert_receiver_driver::send_alert_rsps();
  alert_seq_item item;

  while (!cfg.in_reset) begin
    // Clear the item variable (so that we can tell whether the fork below gets an item or sees a
    // reset)
    item = null;

    fork : isolation_fork begin
      fork
        wait (cfg.in_reset);
        m_pending_alert_rsps.get(item);
      join_any
      disable fork;
    end join

    // If there is an item, send it with send_alert_rsp. The task will exit early on reset.
    if (item != null) begin
      send_alert_rsp(item);

      // Now that the item has been sent, report this to the sequencer
      seq_item_port.put_response(item);
    end
  end

  // When we get here, we must be in reset. m_pending_alert_rsps might be nonempty. (This probably
  // shouldn't actually be possible, but let's not worry too much about it). Report all the items
  // done (in a trivial way) before returning.
  while(m_pending_alert_rsps.try_get(item)) seq_item_port.put_response(item);
endtask

task alert_receiver_driver::send_ping(alert_seq_item item);
  `uvm_info(get_full_name(), "Sending ping", UVM_HIGH)

  if (item.m_int_err_cyc) begin
    `uvm_info(get_full_name(),
              "Not actually sending ping (because m_int_err_cyc is positive)",
              UVM_HIGH)
  end else begin
    drive_alert_ping(item.ping_delay, item.ack_delay, item.ack_stable);
  end
endtask

task alert_receiver_driver::send_alert_rsp(alert_seq_item item);
  `uvm_info(get_full_name(), "Responding to alert", UVM_HIGH)

  // If we get here then something should have been pushed onto the alert queue in response to
  // an alert being generated. Wait a short time to allow the alert to propagate through the
  // clocking blocks (which should only take a cycle, but give it a couple more to make sure).
  // The count of 7 cycles was chosen as an upper bound: an alert should be visible in at most that
  // time.
  //
  // Either way, we stop as soon as the alert propagates through, or if we see a reset.
  wait_for_alert_propagation(7);
  if (cfg.in_reset) return;

  // Check that the alert really has arrived (which is a consistency check for the testbench, rather
  // than a check about the dut).
  if (cfg.vif.receiver_cb.alert_tx.alert_p !== 1'b1) begin
    `uvm_fatal(get_full_name(), "alert_p not high, despite an item from the monitor")
  end

  // Now send an ack with ack_alert. This then waits for the alert to drop, then clears the ack
  // again.
  //
  // The task exits early on reset.
  ack_alert(item.ack_delay, item.ack_stable);
endtask

task alert_receiver_driver::wait_for_alert_propagation(int unsigned max_cycles);
  fork : isolation_fork begin
    fork
      wait (cfg.in_reset);
      fork : isolation_fork begin
        bit seen_alert;

        fork
          repeat (max_cycles) begin
            if (cfg.vif.receiver_cb.alert_tx.alert_p) begin
              seen_alert = 1;
            end
            if (seen_alert) break;
            @(cfg.vif.receiver_cb);
          end
          repeat (max_cycles) begin
            if (cfg.vif.monitor_cb.alert_tx_final.alert_p) begin
              seen_alert = 1;
            end
            if (seen_alert) break;
            @(cfg.vif.monitor_cb);
          end
        join
      end join
    join_any
    disable fork;
  end join
endtask

task alert_receiver_driver::drive_alert_ping(int unsigned ping_delay,
                                             int unsigned ack_delay,
                                             int unsigned ack_stable);
  // Wait for ping_delay cycles (which might be quite a while) before sending the ping. There may be
  // other alerts happening in the meantime, but this task doesn't need to worry about them. Exit
  // early on reset
  fork : isolation_fork begin
    fork
      wait(cfg.in_reset);
      begin
        repeat (ping_delay) @(cfg.vif.receiver_cb);
        set_ping();
      end
    join_any
    disable fork;
  end join
  if (cfg.in_reset) return;

  // After waiting (possibly for a long time), we finally sent a ping. The alert sender should
  // respond with an alert, which we ack here, treating it as the ping response.
  //
  // If the sender decided to send an alert at the same time as we sent the ping then we'll treat
  // that alert as a ping response. But the sender will then respond to the ping with an alert that
  // we'll treat as a genuine alert: the end result will be that we and the sender agree on the set
  // of things that happened (one ping response and one genuine alert).
  ack_alert(ack_delay, ack_stable);

  // Before responding to the item, we need to wait for the sender to complete its FSM (so that we
  // don't send another ping when it's still sitting in PingHsPhase2, Pause0 or Pause1). The ack
  // that we just sent has to be decoded by a prim_diff_decode (u_decode_ack), which will take at
  // most 3 posedges of the sender's clock, then we take two more cycles (one in each of Pause0 and
  // Pause1), for a total of 5 cycles.
  //
  // Wait with the slower of vif.clk and vif.async_clk.
  wait_slower_clock(5);
endtask

task alert_receiver_driver::ack_alert(int unsigned ack_delay, int unsigned ack_stable);
  if (!cfg.use_seq_item_ack_delay) begin
    ack_delay = $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);
  end
  if (!cfg.use_seq_item_ack_stable) begin
    ack_stable = $urandom_range(cfg.ack_stable_max, cfg.ack_stable_min);
  end

  if (cfg.fast_rcvr) begin
    ack_delay = cfg.ack_delay_min;
    ack_stable = cfg.ack_stable_min;
  end

  m_ack_semaphore.get();

  // Wait for the alert to appear (up to cfg.handshake_timeout_cycle cycles)
  fork : isolation_fork1 begin
    fork
      wait(cfg.in_reset);
      repeat(cfg.handshake_timeout_cycle) @(cfg.vif.receiver_cb);
      wait(cfg.vif.receiver_cb.alert_tx.alert_p);
    join_any
    disable fork;
  end join

  // If there has been a reset or no alert came out, there is nothing more to do.
  if (cfg.in_reset || (cfg.vif.receiver_cb.alert_tx.alert_p !== 1'b1)) begin
    m_ack_semaphore.put();
    return;
  end

  // Now wait a short time and set the ack (dropping out early on reset)
  fork : isolation_fork2 begin
    fork
      wait(cfg.in_reset);
      begin
        repeat (ack_delay + 1) @(cfg.vif.receiver_cb);
        set_ack(1'b1);
      end
    join_any
    disable fork;
  end join
  if (cfg.in_reset) begin
    m_ack_semaphore.put();
    return;
  end

  // Finally, wait for the alert to be cleared again (up to cfg.handshake_timeout_cycle cycles)
  fork : isolation_fork3 begin
    fork
      wait(cfg.in_reset);
      repeat(cfg.handshake_timeout_cycle) @(cfg.vif.receiver_cb);
      begin
        wait(!cfg.vif.receiver_cb.alert_tx.alert_p);
        repeat (ack_stable) @(cfg.vif.receiver_cb);
        set_ack(1'b0);
      end
    join_any
    disable fork;
  end join

  m_ack_semaphore.put();
endtask

task alert_receiver_driver::set_ack(bit asserted);
  cfg.vif.receiver_cb.alert_rx_int.ack_p <= asserted;
  cfg.vif.receiver_cb.alert_rx_int.ack_n <= !asserted;
endtask

task alert_receiver_driver::set_ping();
  cfg.vif.receiver_cb.alert_rx_int.ping_p <= !cfg.vif.alert_rx.ping_p;
  cfg.vif.receiver_cb.alert_rx_int.ping_n <= !cfg.vif.alert_rx.ping_n;
endtask

task alert_receiver_driver::reset_ping();
  cfg.vif.receiver_cb.alert_rx_int.ping_p <= 1'b0;
  cfg.vif.receiver_cb.alert_rx_int.ping_n <= 1'b1;
endtask

task alert_receiver_driver::do_alert_rx_init();
  fork : isolation_fork begin
    fork
      wait(cfg.in_reset);
      begin
        repeat ($urandom_range(1, 10)) @(cfg.vif.receiver_cb);
        cfg.vif.alert_rx_int.ack_p <= 1'b0;
        cfg.vif.alert_rx_int.ack_n <= 1'b0;

        wait (cfg.vif.receiver_cb.alert_tx.alert_p == cfg.vif.receiver_cb.alert_tx.alert_n);
        repeat ($urandom_range(1, 10)) @(cfg.vif.receiver_cb);
        cfg.vif.alert_rx_int.ack_n <= 1'b1;

        wait (cfg.vif.receiver_cb.alert_tx.alert_p != cfg.vif.receiver_cb.alert_tx.alert_n);
      end
    join_any
    disable fork;
  end join
endtask

task alert_receiver_driver::wait_slower_clock(int unsigned num_cycles);
  fork : isolation_fork begin
    fork
      wait(cfg.in_reset);
      fork
        repeat (num_cycles) @(posedge cfg.vif.clk);
        repeat (num_cycles) @(posedge cfg.vif.async_clk);
      join
    join_any
    disable fork;
  end join
endtask
