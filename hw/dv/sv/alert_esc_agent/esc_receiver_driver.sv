// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Alert_handler receiver driver
// ---------------------------------------------
class esc_receiver_driver extends alert_esc_base_driver;

  `uvm_component_utils(esc_receiver_driver)

  `uvm_component_new

  bit is_ping;

  virtual task reset_signals();
    do_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      under_reset = 1;
      do_reset();
      is_ping = 0;
      @(posedge cfg.vif.rst_n);
      under_reset = 0;
    end
  endtask

  virtual task drive_req();
    fork
      rsp_escalator();
      esc_ping_detector();
    join_none
  endtask : drive_req

  virtual task esc_ping_detector();
    forever begin
      int cnt ;
      wait(under_reset == 0);
      fork
        begin
          wait_esc();
          @(cfg.vif.receiver_cb);
          while (get_esc() == 1) begin
            cnt++;
            @(cfg.vif.receiver_cb);
          end
          if (cnt == 1) is_ping = 1;
        end
        begin
          wait(under_reset);
        end
      join_any
      disable fork;
    end
  endtask

  // This task will response to escalator sender's esc_p and esc_n signal,
  // depending on the signal length and req setting, it will response to
  // ping and real esc signals.
  // Once a request is received, the task uses non-blocking fork to allow other requests to be
  // received and processed in parallel.
  virtual task rsp_escalator();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_esc_rsp_q.size() > 0 && !under_reset);
      req = r_esc_rsp_q.pop_front();
      `downcast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn, $sformatf("starting to send receiver item, esc_rsp=%0b int_fail=%0b",
                req.r_esc_rsp, req.int_err), UVM_HIGH)
      fork
        begin : non_blocking_fork
          fork
            drive_esc_resp(req);
            wait(under_reset);
          join_any
          disable fork;
          `uvm_info(`gfn, $sformatf("finished sending receiver item esc_rsp=%0b int_fail=%0b",
                    req.r_esc_rsp, req.int_err), UVM_HIGH)
          seq_item_port.put_response(rsp);
        end
      join_none
    end // end forever
  endtask : rsp_escalator

  // this task drives resp_p/n according to the req
  // if req is "standalone_sig_int_err", will wait until no esc_p/n, then random toggle resp_p/n
  // if esc_p/n is esc signal, will toggle resp_p/n until esc_p is reset back to 0
  // if esc_p/n is ping, then will toggle resp_p/n for two clk cycles
  // if req is "sig_int_err", will random toggle, then reset back to resp_p/n = {0/1}
  virtual task drive_esc_resp(alert_esc_seq_item req);
    if (req.standalone_int_err) begin
      wait_esc_complete();
      @(cfg.vif.receiver_cb); // wait one clock cycle to ensure is_ping is set
      if (!is_ping) begin
        repeat (req.int_err_cyc) begin
          if (cfg.vif.esc_tx.esc_p === 1'b0 && !is_ping) begin
            random_drive_resp_signal();
            @(cfg.vif.receiver_cb);
          end else begin
            break;
          end
        end
        // TODO: missed int_err case at first cycle of the esc_p = 1
        if (!is_ping) reset_resp();
      end
    end else begin
      wait_esc();
      @(cfg.vif.receiver_cb);
      while (get_esc() === 1'b1) toggle_resp_signal(req.int_err);

      // drives escalation ping request response according to the above scenarios:
      // if no sig_int_err: the driver will toggle resp_p/n as design required
      // if there is sig_int_err: the driver will randomly toggle resp_p/n until ping timeout
      // if ping is interrupted by real esclation signal: the ping response is aborted
      // immediately and response to the real escalation signal without sig_int_err
      if (is_ping) begin
        // `ping_timeout_cycle` is divided by 2 because `toggle_resp_signal` task contains two cycles
        int toggle_cycle = req.int_err ? cfg.ping_timeout_cycle / 2 : 1;
        fork
          begin : isolation_fork
            fork
              repeat (toggle_cycle) toggle_resp_signal(req.ping_timeout);
              cfg.probe_vif.wait_esc_en();
            join_any
            disable fork;
          end
        join
        is_ping = 0;
        if (cfg.probe_vif.get_esc_en()) begin
          while (get_esc() === 1'b1) toggle_resp_signal(0);
        end
      end
      if (req.ping_timeout || req.int_err) reset_resp();
    end
  endtask

  // If do not request int_err: Toggle resp_p/n for two cycles,
  // first cycle drives resp_p = 1, resp_n = 0; second cycle drives resp_p = 0, resp_n = 1
  // If request int_err: random drives resp_p/n for two cycles
  task toggle_resp_signal(bit do_int_err);
    bit first_cycle_finished;
    repeat(2) begin
      if (do_int_err) random_drive_resp_signal();
      else begin
        if (!first_cycle_finished) set_resp();
        else reset_resp();
      end
      @(cfg.vif.receiver_cb);
      first_cycle_finished = 1;
    end
  endtask : toggle_resp_signal

  task random_drive_resp_signal();
    randcase
      1: set_resp();
      1: reset_resp();
      1: set_resp_both_high();
      1: set_resp_both_low();
    endcase
  endtask

  virtual task set_resp();
    cfg.vif.receiver_cb.esc_rx_int.resp_p <= 1'b1;
    cfg.vif.receiver_cb.esc_rx_int.resp_n <= 1'b0;
  endtask

  virtual task reset_resp();
    cfg.vif.receiver_cb.esc_rx_int.resp_p <= 1'b0;
    cfg.vif.receiver_cb.esc_rx_int.resp_n <= 1'b1;
  endtask

  virtual task set_resp_both_high();
    cfg.vif.receiver_cb.esc_rx_int.resp_p <= 1'b1;
    cfg.vif.receiver_cb.esc_rx_int.resp_n <= 1'b1;
  endtask

  virtual task set_resp_both_low();
    cfg.vif.receiver_cb.esc_rx_int.resp_p <= 1'b0;
    cfg.vif.receiver_cb.esc_rx_int.resp_n <= 1'b0;
  endtask

  virtual function bit get_esc();
    return cfg.vif.receiver_cb.esc_tx.esc_p && !cfg.vif.receiver_cb.esc_tx.esc_n;
  endfunction

  virtual task wait_esc_complete();
    while (cfg.vif.esc_tx.esc_p === 1'b1 && cfg.vif.esc_tx.esc_n === 1'b0) @(cfg.vif.receiver_cb);
  endtask

  virtual task wait_esc();
    while (cfg.vif.esc_tx.esc_p === 1'b0 && cfg.vif.esc_tx.esc_n === 1'b1) @(cfg.vif.receiver_cb);
  endtask : wait_esc

  virtual task do_reset();
    cfg.vif.esc_rx_int.resp_p <= 1'b0;
    cfg.vif.esc_rx_int.resp_n <= 1'b1;
  endtask

endclass : esc_receiver_driver
