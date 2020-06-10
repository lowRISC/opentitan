// Copyright lowRISC contributors.
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
    forever begin
      @(negedge cfg.vif.rst_n);
      reset_resp();
      is_ping = 0;
      @(posedge cfg.vif.rst_n);
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
      wait_esc();
      @(cfg.vif.receiver_cb);
      while (get_esc() == 1) begin
        cnt++;
        @(cfg.vif.receiver_cb);
      end
      if (cnt == 1) is_ping = 1;
    end
  endtask

  // This task will response to escalator sender's esc_p and esc_n signal,
  // depending on the signal length and req setting, it will response to
  // ping and real esc signals.
  virtual task rsp_escalator();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_esc_rsp_q.size() > 0);
      req = r_esc_rsp_q.pop_front();
      fork
        begin
          $cast(rsp, req.clone());
          rsp.set_id_info(req);
          `uvm_info(`gfn,
              $sformatf("starting to send receiver item, esc_rsp=%0b int_fail=%0b",
              req.r_esc_rsp, req.int_err), UVM_HIGH)

          if (req.standalone_int_err) begin
            wait_esc_complete();
            if (!is_ping) begin
              repeat (req.int_err_cyc) begin
                if (cfg.vif.esc_tx.esc_p === 1'b0 && !is_ping) begin
                  random_drive_resp_signal();
                  @(cfg.vif.receiver_cb);
                end else begin
                  break;
                end
              end
              // TODO: missed int_err case at cycle when first cycle of the esc_p set
              if (!is_ping) reset_resp();
            end
          end else begin
            wait_esc();
            @(cfg.vif.receiver_cb);
            while (get_esc() === 1'b1) toggle_resp_signal(req);
            if (is_ping) begin
              int toggle_cycle = 1;
              if (req.int_err) toggle_cycle = $urandom_range(0, cfg.ping_timeout_cycle);
              repeat (toggle_cycle) toggle_resp_signal(req);
              is_ping = 0;
            end
            if (req.int_err) reset_resp();
          end
          `uvm_info(`gfn,
              $sformatf("finished sending receiver item esc_rsp=%0b int_fail=%0b",
              req.r_esc_rsp, req.int_err), UVM_HIGH)
          seq_item_port.put_response(rsp);
        end
      join_none
    end // end forever
  endtask : rsp_escalator

  task toggle_resp_signal(alert_esc_seq_item req);
    if (req.int_err) random_drive_resp_signal();
    else set_resp();
    @(cfg.vif.receiver_cb);

    if (req.int_err) random_drive_resp_signal();
    else reset_resp();
    @(cfg.vif.receiver_cb);
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
    cfg.vif.receiver_cb.esc_rx.resp_p <= 1'b1;
    cfg.vif.receiver_cb.esc_rx.resp_n <= 1'b0;
  endtask

  virtual task reset_resp();
    cfg.vif.receiver_cb.esc_rx.resp_p <= 1'b0;
    cfg.vif.receiver_cb.esc_rx.resp_n <= 1'b1;
  endtask

  virtual task set_resp_both_high();
    cfg.vif.receiver_cb.esc_rx.resp_p <= 1'b1;
    cfg.vif.receiver_cb.esc_rx.resp_n <= 1'b1;
  endtask

  virtual task set_resp_both_low();
    cfg.vif.receiver_cb.esc_rx.resp_p <= 1'b0;
    cfg.vif.receiver_cb.esc_rx.resp_n <= 1'b0;
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

endclass : esc_receiver_driver
