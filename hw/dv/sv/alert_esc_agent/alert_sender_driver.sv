// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler sender driver
// ---------------------------------------------
class alert_sender_driver extends alert_esc_base_driver;

  `uvm_component_utils(alert_sender_driver)

  `uvm_component_new

  // To guard alert ping response and real alert triggers won't trigger at the same time
  semaphore alert_atomic = new(1);

  virtual task reset_signals();
    under_reset = 1;
    do_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      do_reset();
      @(posedge cfg.vif.rst_n);
      void'(alert_atomic.try_get(1));
      alert_atomic.put(1);
    end
  endtask

  // alert_sender drive responses by sending the alert_p and alert_n
  // one alert sent by sequence driving the alert_send signal
  // another alert sent by responding to the ping signal
  virtual task drive_req();
    fork
      send_alert();
      rsp_ping();
      alert_init_thread();
    join_none
  endtask : drive_req

  // Two conditions can trigger alert init:
  // 1). Reset deassert;   2). LPG disabled.
  virtual task alert_init_thread();
    do_alert_tx_init();
    fork
      forever @(posedge cfg.vif.rst_n) begin
        do_alert_tx_init();
      end
      forever @(negedge cfg.en_alert_lpg) begin
        do_alert_tx_init();
      end
    join_none
  endtask : alert_init_thread

  virtual task send_alert();
    forever begin
      alert_esc_seq_item req, rsp;
      wait (s_alert_send_q.size() > 0 && !under_reset);
      req = s_alert_send_q.pop_front();
      `downcast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
      fork
        begin : isolation_fork
          fork
            begin
              alert_atomic.get(1);
              drive_alert_pins(req);
              alert_atomic.put(1);
            end
            begin
              wait (under_reset);
            end
          join_any
          disable fork;
        end
      join

      `uvm_info(`gfn,
          $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end // end forever
  endtask : send_alert

  virtual task rsp_ping();
    forever begin
      alert_esc_seq_item req, rsp;
      wait (s_alert_ping_rsp_q.size() > 0 && !under_reset && !cfg.en_alert_lpg);
      req = s_alert_ping_rsp_q.pop_front();
      `downcast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)

      `DV_SPINWAIT_EXIT(
          alert_atomic.get(1);
          if (!cfg.ping_timeout) begin
            drive_alert_pins(req);
          end else begin
            repeat (cfg.ping_timeout_cycle) wait_sender_clk();
          end
          alert_atomic.put(1);,
          wait (under_reset || cfg.en_alert_lpg);)

      `uvm_info(`gfn,
          $sformatf("finished sending sender item, alert_send=%0b, ping_rsp=%0b, int_err=%0b",
          req.s_alert_send, req.s_alert_ping_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end
  endtask : rsp_ping

  virtual task drive_alert_pins(alert_esc_seq_item req);
    int unsigned alert_delay, ack_delay;
    alert_delay = (cfg.use_seq_item_alert_delay) ? req.alert_delay :
        $urandom_range(cfg.alert_delay_max, cfg.alert_delay_min);
    ack_delay = (cfg.use_seq_item_ack_delay) ? req.ack_delay :
        $urandom_range(cfg.ack_delay_max, cfg.ack_delay_min);

    if (!req.int_err) begin
      set_alert_pins(alert_delay);
      reset_alert_pins(ack_delay);

    // alert signals integrity fail
    end else begin
      if (req.alert_int_err_type & HasAlertBeforeIntFailOnly) set_alert_pins(alert_delay);
      random_drive_int_fail(req.int_err_cyc);
      if (req.alert_int_err_type & HasAlertAfterIntFailOnly) begin
        set_alert_pins(alert_delay);
      end else begin
        reset_alert();
      end
    end

    // there must have at least two sender clock delays before next alert_handshake
    repeat(2) wait_sender_clk();
  endtask : drive_alert_pins

  // this task set alert_p=1 and alert_n=0 after certain delay
  virtual task set_alert_pins(int alert_delay);
    repeat (alert_delay + 1) begin
      if (under_reset) return;
      else wait_sender_clk();
    end
    set_alert();
  endtask : set_alert_pins

  // this task reset alert_p=0 and alert_n=1 after certain delay when:
  // ack handshake is finished or when timeout
  virtual task reset_alert_pins(int ack_delay);
    fork
      begin : isolation_fork
        fork
          begin : alert_timeout
            repeat (cfg.handshake_timeout_cycle) begin
              wait_sender_clk();
              // If alert_lpg is enabled, alert rx request is ignored by the alert_receiver.
              if (cfg.en_alert_lpg) break;
            end
          end
          begin : wait_alert_handshake
            wait (cfg.vif.alert_rx.ack_p == 1'b1);
            wait_sender_clk();
            repeat (ack_delay) wait_sender_clk();
            reset_alert();
            wait (cfg.vif.alert_rx.ack_p == 1'b0);
          end
        join_any
        disable fork;
      end
    join
  endtask : reset_alert_pins

  virtual task random_drive_int_fail(int int_err_cyc);
    repeat (req.int_err_cyc) begin
      wait_sender_clk();
      if (under_reset) break;
      randcase
        1: drive_alerts_low();
        1: drive_alerts_high();
      endcase
    end
  endtask : random_drive_int_fail

  virtual task set_alert();
    cfg.vif.sender_cb.alert_tx_int.alert_p <= 1'b1;
    cfg.vif.sender_cb.alert_tx_int.alert_n <= 1'b0;
  endtask

  virtual task reset_alert();
    cfg.vif.sender_cb.alert_tx_int.alert_p <= 1'b0;
    cfg.vif.sender_cb.alert_tx_int.alert_n <= 1'b1;
  endtask

  virtual task drive_alerts_high();
    cfg.vif.sender_cb.alert_tx_int.alert_p <= 1'b1;
    cfg.vif.sender_cb.alert_tx_int.alert_n <= 1'b1;
  endtask

  virtual task drive_alerts_low();
    cfg.vif.sender_cb.alert_tx_int.alert_p <= 1'b0;
    cfg.vif.sender_cb.alert_tx_int.alert_n <= 1'b0;
  endtask

  virtual task wait_sender_clk();
    @(cfg.vif.sender_cb);
  endtask

  virtual task do_reset();
    cfg.vif.alert_tx_int.alert_p <= 1'b0;
    cfg.vif.alert_tx_int.alert_n <= 1'b1;
  endtask

  // This task handles alert init request.
  //
  // After alert_receiver is reset, it will send a signal integrity fail via `ping_n` and `ack_n`,
  // alert_sender acknowledged the init via sending an `alert_n` integrity fail.
  virtual task do_alert_tx_init();
    fork begin
      fork
        begin
          wait (cfg.vif.alert_rx.ack_p == cfg.vif.alert_rx.ack_n);
          cfg.vif.alert_tx_int.alert_n <= 1'b0;
          wait (cfg.vif.alert_rx.ack_p != cfg.vif.alert_rx.ack_n);
          cfg.vif.alert_tx_int.alert_n <= 1'b1;
          under_reset = 0;
        end
        begin
          @(negedge cfg.vif.rst_n);
        end
        begin
          // Clear `under_reset` when en_alert_lpg is on, because alert_sender can still send
          // alerts, and alert_handler should ignore the alert_tx request.
          wait (cfg.en_alert_lpg == 1);
          under_reset = 0;
        end
      join_any
      disable fork;
    end
    join
  endtask

endclass : alert_sender_driver
