// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler sender driver
// ---------------------------------------------
class alert_sender_driver extends alert_base_driver;

  `uvm_component_utils(alert_sender_driver)

  // An event that can be triggered (by functions as well as tasks). This is monitored by
  // maintain_alert_drive, which will call cfg.vif.force_alert with m_desired_alert_val.
  uvm_event m_update_alert_val;
  bit [1:0] m_desired_alert_val;

  extern function new (string name, uvm_component parent);

  // This function gets called by dv_base_driver::reset_signals when the interface enters reset.
  // Clear any alert signal.
  extern virtual function void on_enter_reset();

  // Drive sequence items for alerts and pings that have been retrieved by get_req (and therefore
  // have started) and have been pushed to the various queues. This also does the alert init
  // handshake (with no sequence item) after each reset.
  //
  // An implementation of alert_esc_base_driver::drive_req
  extern virtual task drive_req();

  // Drive sequence items for alerts and pings until either a reset or a change of cfg.en_alert_lpg
  extern local task drive_reqs_with_lpg_mode(bit en_alert_lpg);

  // Drive a single sequence item to send an alert, possibly responding to a ping. Once the item has
  // been driven, mark it done in seq_item_port.
  //
  // This exits immediately on a reset.
  extern local task send_item(bit is_ping_rsp, alert_esc_seq_item item);

  // Drive the alert_p/alert_n pins for the sequence item. There may be a delay before asserting the
  // alert or before de-asserting it (once an ack has been seen).
  //
  // This is safe to kill.
  extern local task drive_alert_pins(alert_esc_seq_item req);

  // Assert an alert (alert_p=1; alert_n=0) after alert_delay cycles.
  //
  // This is safe to kill.
  extern local task set_alert_pins(int alert_delay);

  // Wait for an ack from the receiver, then de-assert the alert (alert_p=0; alert_n=1) after an
  // extra ack_delay cycles. Finally, wait for the receiver to de-assert ack.
  //
  // The handshake above has a timeout, and the task will exit if it is reached. If cfg.en_alert_lpg
  // becomes false, this means that the receiver will no longer respond. We regard that as an
  // immediate timeout.
  //
  // This is safe to kill.
  extern local task reset_alert_pins(int ack_delay);

  // Send invalid alert pin values (either 11 or 00) for int_err_cyc cycles
  //
  // This is safe to kill.
  extern local task random_drive_int_fail(int int_err_cyc);

  // Set the alert pins to be (alert_p=1; alert_n=0) if enabled=1 and (alert_p=0; alert_n=1)
  // otherwise.
  //
  // Because the alert signals are set through a clocking block (using cfg.vif.force_alert()), this
  // works by setting m_desired_alert_val and triggering the m_update_alert_val event.
  extern local function void set_alert(bit enabled);

  // Set the alert pins to 11 or 00 (depending on the high argument).
  //
  // This task takes zero time (but needs to be a task because it uses non-blocking assignment)
  extern local task drive_invalid_alert(bit high);

  // Wait for count cycles of the sender clock
  //
  // This is safe to kill.
  extern local task wait_sender_clk(int unsigned count);

  // Handle an alert init request.
  //
  // After alert_receiver is reset, it will send a signal integrity fail with a non-differential ack
  // signal. The alert sender has to acknowledge the init by setting the alert pins to 00 until ack
  // becomes differential again.
  //
  // This task exits early on reset or if cfg.en_alert_lpg is asserted (in which case, the receiver
  // won't reply to the init)
  extern local task do_alert_tx_init();

  // This task runs forever, calling cfg.vif.set_alert() each time the m_update_alert_val event is
  // triggered.
  extern local task maintain_alert_drive();
endclass : alert_sender_driver

function alert_sender_driver::new (string name, uvm_component parent);
  super.new(name, parent);
  m_update_alert_val = new("m_update_alert_val");
endfunction

function void alert_sender_driver::on_enter_reset();
  set_alert(1'b0);
endfunction

task alert_sender_driver::drive_req();
  fork
    maintain_alert_drive();
    forever begin
      // Wait until we are out of reset. Until that happens, respond instantly to any sequence items
      // that come in.
      while (cfg.in_reset) begin
        fork : isolation_fork begin
          alert_esc_seq_item item;
          fork
            wait(!cfg.in_reset);
            m_sender_requests.get(item);
          join_any
          disable fork;
          if (item != null) seq_item_port.put_response(item);
        end join
      end

      while(!cfg.in_reset) begin
        bit en_alert_lpg = cfg.en_alert_lpg;

        // If LPG is not enabled, initialise the alert interface
        if (!en_alert_lpg) begin
          do_alert_tx_init();
        end

        // Drive any requests that we see. The task will exit on reset or if the LPG flag changes,
        // letting us initialise the alert interface (if LPG is disabled) and continue.
        drive_reqs_with_lpg_mode(en_alert_lpg);
      end
    end
  join
endtask

task alert_sender_driver::drive_reqs_with_lpg_mode(bit en_alert_lpg);
  forever begin
    alert_esc_seq_item item;
    bit is_alert, is_ping;

    // Pick an item to drive, but keep track of resets and any change to the LPG flag.
    fork : isolation_fork begin
      fork
        wait(cfg.en_alert_lpg != en_alert_lpg);
        wait(cfg.in_reset);
        m_sender_requests.get(item);
      join_any
      disable fork;
    end join

    // If there is no item, there has been a reset or the LPG flag has changed. Return from the
    // task.
    if (item == null) return;

    // Handle the alert request or ping response. If the item requests both, send the ping response
    // first and then the real alert.
    if (item.s_alert_ping_rsp) send_item(1'b1, item);
    if (item.s_alert_send) send_item(1'b0, item);
    seq_item_port.put_response(item);
  end
endtask

task alert_sender_driver::send_item(bit is_ping_rsp, alert_esc_seq_item item);
  `uvm_info(`gfn,
            $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
                      req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
  fork : isolation_fork begin
    fork
      wait(cfg.in_reset);
      if (!is_ping_rsp || !cfg.ping_timeout) begin
        drive_alert_pins(item);
      end else begin
        wait_sender_clk(cfg.ping_timeout_cycle);
      end
    join_any
    disable fork;
  end join
  `uvm_info(`gfn,
            $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
                      req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
endtask

task alert_sender_driver::drive_alert_pins(alert_esc_seq_item req);
  int unsigned alert_delay, ack_delay;
  alert_delay = (cfg.use_seq_item_alert_delay) ? req.alert_delay :
                $urandom_range(cfg.alert_delay_max, cfg.alert_delay_min);
  ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
              $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);

  if (!req.int_err) begin
    set_alert_pins(alert_delay);
    reset_alert_pins(ack_delay);
  end else begin
    // Because req.int_err is true, cause the alert signal integrity check to fail.
    if (req.alert_int_err_type & HasAlertBeforeIntFailOnly) set_alert_pins(alert_delay);
    random_drive_int_fail(req.int_err_cyc);
    if (req.alert_int_err_type & HasAlertAfterIntFailOnly) begin
      set_alert_pins(alert_delay);
    end else begin
      set_alert(1'b0);
    end
  end

  // there must have at least two sender clock delays before next alert_handshake
  wait_sender_clk(2);
endtask

task alert_sender_driver::set_alert_pins(int alert_delay);
  wait_sender_clk(alert_delay + 1);
  set_alert(1'b1);
endtask

task alert_sender_driver::reset_alert_pins(int ack_delay);
  fork : isolation_fork begin
    fork
      wait(cfg.en_alert_lpg);
      wait_sender_clk(cfg.handshake_timeout_cycle);
      begin : wait_alert_handshake
        wait (cfg.vif.alert_rx.ack_p == 1'b1);
        wait_sender_clk(1 + ack_delay);
        set_alert(1'b0);
        wait (cfg.vif.alert_rx.ack_p == 1'b0);
      end
    join_any
    disable fork;
  end join
endtask

task alert_sender_driver::random_drive_int_fail(int int_err_cyc);
  repeat (req.int_err_cyc) begin
    wait_sender_clk(1);
    drive_invalid_alert($urandom & 1);
  end
endtask

function void alert_sender_driver::set_alert(bit enabled);
  m_desired_alert_val = {enabled, !enabled};
  m_update_alert_val.trigger();
endfunction

task alert_sender_driver::drive_invalid_alert(bit high);
  cfg.vif.sender_cb.alert_tx_int.alert_p <= high;
  cfg.vif.sender_cb.alert_tx_int.alert_n <= high;
endtask

task alert_sender_driver::wait_sender_clk(int unsigned count);
  repeat (count) @(cfg.vif.sender_cb);
endtask

task alert_sender_driver::do_alert_tx_init();
  fork : isolation_fork begin
    fork
      wait(cfg.in_reset || cfg.en_alert_lpg);
      begin
        wait (cfg.vif.alert_rx.ack_p == cfg.vif.alert_rx.ack_n);
        drive_invalid_alert(1'b0);
        wait (cfg.vif.alert_rx.ack_p != cfg.vif.alert_rx.ack_n);
        set_alert(1'b0);
      end
    join_any
    disable fork;
  end join
endtask

task alert_sender_driver::maintain_alert_drive();
  forever begin
    m_update_alert_val.wait_ptrigger();
    cfg.vif.force_alert(m_desired_alert_val[1], m_desired_alert_val[0]);
    m_update_alert_val.reset();
  end
endtask
