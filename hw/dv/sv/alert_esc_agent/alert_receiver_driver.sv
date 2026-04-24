// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A driver that behaves as an alert_receiver. This is used in alert_esc_agent when configured in
// "device mode"

class alert_receiver_driver extends alert_base_driver;
  `uvm_component_utils(alert_receiver_driver)

  // A pair of ids that can be used as a key for a sequence item. We need the sequence ID as well as
  // the transaction ID so that we can distinguish items at the same position in different
  // sequences. The types are chosen to match UVM's get_transaction_id and get_sequence_id.
  typedef struct packed {
    int     sequence_id;
    integer transaction_id;
  } id_pair_t;

  // The drive_req_between_resets task will consume requests from m_receiver_requests and add these
  // requests to this pair of FIFOs (to be consumed by the send_pings and send_alert_rsps tasks that
  // it spawns).
  //
  // When reset is asserted, both of those tasks will exit after flushing their respective queues.
  local uvm_tlm_analysis_fifo #(alert_esc_seq_item) m_pending_pings;
  local uvm_tlm_analysis_fifo #(alert_esc_seq_item) m_pending_alert_rsps;

  // A map from item transaction ID to the tasks that are pending for that item. If bit 0 is set,
  // the item represents an alert that must be responded to. If bit 1 is set, the item represents a
  // ping request.
  //
  // When the send_pings or send_alert_rsps task clears the final bit for an item, it should remove
  // the item from this map. Because the base driver uses get (instead of get_next_item), we don't
  // also have to call seq_item_port.item_done to tell the sequencer that the item has been fully
  // driven, but we *do* send a response (by sending the original item), to allow the sequence to
  // see that the item is done.
  //
  // When reset is asserted, both of those tasks will exit, clearing this map.
  local bit [1:0] m_transaction_tasks[id_pair_t];

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

  // Drive requests that have been seen by alert_base_driver::get_req, until the next reset. This is
  // called by drive_req.
  extern local task drive_req_between_resets();

  // Clear the appropriate bit in m_transaction_tasks for the ID pair of item. If the resulting
  // bitmap is zero, delete the entry from m_transaction_tasks.
  extern local function void report_done(bit is_ping, alert_esc_seq_item item);

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
  extern local task send_ping(alert_esc_seq_item item);

  // Handle a sequence item that demands an alert response
  //
  // An item should only be added to that queue in response to an alert being generated on the
  // interface. We will wait a randomised time (in ack_alert) before acknowledging the alert.
  //
  // Exits early on reset.
  extern local task send_alert_rsp(alert_esc_seq_item item);

  // Wait for a short time to allow an alert to propagate through the clocking blocks in the
  // interface, stopping as soon as it gets through to receiver_cb.alert_tx or
  // monitor_cb.alert_tx_final or a reset happens.
  //
  // Exits early on reset.
  extern local task wait_for_alert_propagation();

  // Drive an alert ping
  //
  // This will start by waiting between cfg.ping_delay_min and cfg.ping_delay_max cycles before
  // sending the ping request. If cfg.use_seq_item_ping_delay is true then the delay is from the
  // ping_delay argument.
  //
  // Once the ping has gone out, we wait for an alert to arrive and then acknowledge it using
  // ack_alert (and passing ack_delay and ack_stable).
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
        alert_esc_seq_item item;
        fork
          wait (!cfg.in_reset);
          m_receiver_requests.get(item);
        join_any
        disable fork;
        // Since we are in reset, we ignore any item that we see. Because it was fetched by get() in
        // alert_base_driver (instead of with get_next_item()), we do not have to declare it done.
      end join
    end

    drive_req_between_resets();
  end
endtask

task alert_receiver_driver::drive_req_between_resets();
  // Drive the init protocol from the receiver side. do_alert_rx_init will exit early if it sees
  // reset.
  do_alert_rx_init();
  if (cfg.in_reset) return;

  // Fetch items to drive and drive them. All three tasks exit on reset.
  fork
    send_alert_rsps();
    send_pings();
    fork : isolation_fork begin
      fork
        wait (cfg.in_reset);
        forever begin
          alert_esc_seq_item item;
          id_pair_t ids;
          bit [1:0] jobs;

          m_receiver_requests.get(item);
          jobs[0] = item.r_alert_rsp;
          jobs[1] = item.r_alert_ping_send;

          if (!jobs)
            `uvm_fatal(get_full_name(),
                       $sformatf("Item sent to driver doesn't have any tasks for us: %0s",
                                 item.sprint()))

          ids.transaction_id = item.get_transaction_id();
          ids.sequence_id    = item.get_sequence_id();

          if (m_transaction_tasks.exists(ids))
            `uvm_fatal(get_full_name(),
                       $sformatf("Repeated transaction ID: %0d / sequence ID 0x%0x",
                                 ids.transaction_id, ids.sequence_id))

          m_transaction_tasks[ids] = jobs;
          if (jobs[1]) m_pending_pings.write(item);
          if (jobs[0]) m_pending_alert_rsps.write(item);
        end
      join_any
      disable fork;
    end join
  join

  // As a consistency check, make sure that m_pending_pings, m_pending_alert_rsps and
  // m_transaction_tasks were been cleared by send_alert_rsps and send_pings before they exited.
  if (m_pending_pings.size())
    `uvm_error(get_full_name(),
               $sformatf("m_pending_pings nonempty after reset: %0p", m_pending_pings))
  if (m_pending_alert_rsps.size())
    `uvm_error(get_full_name(),
               $sformatf("m_pending_alert_rsps nonempty after reset: %0p", m_pending_alert_rsps))
  if (m_transaction_tasks.size())
    `uvm_error(get_full_name(),
               $sformatf("m_transaction_tasks nonempty after reset: %0p", m_transaction_tasks))

endtask

function void alert_receiver_driver::report_done(bit is_ping, alert_esc_seq_item item);
  id_pair_t ids;
  ids.transaction_id = item.get_transaction_id();
  ids.sequence_id    = item.get_sequence_id();

  if (!m_transaction_tasks.exists(ids))
    `uvm_fatal(get_full_name(),
               $sformatf("Cannot check if item is done: %0s", item.sprint()))

  if (!m_transaction_tasks[ids][is_ping])
    `uvm_fatal(get_full_name(),
               $sformatf("Cannot clear unset bit %0s for item in m_transaction_tasks: %0s",
                         is_ping, item.sprint()))
  m_transaction_tasks[ids][is_ping] = 0;

  if (~|m_transaction_tasks[ids]) begin
    // If we had originally got the item with get_next_item, this would be the right place to call
    // item_done. Since we used get instead (allowing alerts and pings to be driven in parallel), we
    // just send a response (the original item), which allows the sequence that sent the item to
    // know driving it is completed.
    m_transaction_tasks.delete(ids);
    seq_item_port.put_response(item);
  end
endfunction

task alert_receiver_driver::send_pings();
  alert_esc_seq_item item;

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

      // Now that the item has been sent, report this to the sequencer (if this was the last job to
      // do for the item)
      report_done(1, item);
    end
  end

  // When we get here, we must be in reset. m_pending_pings might be nonempty (if reset was asserted
  // when there were lots of pending pings). Report all the items done (in a trivial way) before
  // returning.
  while(m_pending_pings.try_get(item)) report_done(1, item);
endtask

task alert_receiver_driver::send_alert_rsps();
  alert_esc_seq_item item;

  while(!cfg.in_reset) begin
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

      // Now that the item has been sent, report this to the sequencer (if this was the last job to
      // do for the item)
      report_done(0, item);
    end
  end

  // When we get here, we must be in reset. m_pending_alert_rsps might be nonempty. (This probably
  // shouldn't actually be possible, but let's not worry too much about it). Report all the items
  // done (in a trivial way) before returning.
  while(m_pending_alert_rsps.try_get(item)) report_done(0, item);
endtask

task alert_receiver_driver::send_ping(alert_esc_seq_item item);
  `uvm_info(get_full_name(), "Sending ping", UVM_HIGH)

  if (item.int_err) begin
    `uvm_info(get_full_name(), "Not actually sending ping (because int_err is true)", UVM_HIGH)
  end else begin
    drive_alert_ping(item.ping_delay, item.ack_delay, item.ack_stable);
  end
endtask

task alert_receiver_driver::send_alert_rsp(alert_esc_seq_item item);
  `uvm_info(get_full_name(), "Responding to alert", UVM_HIGH)

  // If we get here then something should have been pushed onto the alert queue in response to
  // an alert being generated. Wait a short time to allow the alert to propagate through the
  // clocking blocks (which should only take a cycle, but give it a couple more to make sure).
  // Stop early if we go into reset.
  wait_for_alert_propagation();
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

task alert_receiver_driver::wait_for_alert_propagation();
  int unsigned num_iter = 7;

  fork : isolation_fork begin
    fork
      wait (cfg.in_reset);
      fork : isolation_fork begin
        bit seen_alert;

        fork
          repeat (num_iter) begin
            if (cfg.vif.receiver_cb.alert_tx.alert_p) begin
              seen_alert = 1;
            end
            if (seen_alert) break;
            @(cfg.vif.receiver_cb);
          end
          repeat (num_iter) begin
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
  // Wait for ping_delay cycles before sending the ping request, but exit early on reset
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

  // Respond to the next alert with ack_alert
  ack_alert(ack_delay, ack_stable);
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
