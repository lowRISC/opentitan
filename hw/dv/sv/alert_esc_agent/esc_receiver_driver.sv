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
    cfg.vif.reset_resp();
    is_ping = 0;
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
      cfg.vif.wait_esc();
      @(cfg.vif.receiver_cb);
      while (cfg.vif.get_esc() == 1) begin
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

          // toggle resp signals only when esc signals are not set
          if (req.int_err && req.resp_int_err_type == RandResponse) begin
            cfg.vif.wait_esc_complete();
            repeat (req.int_err_cyc) begin
              if (cfg.vif.get_esc() === 1'b0) begin
                randcase
                  1: cfg.vif.set_resp();
                  1: cfg.vif.reset_resp();
                endcase
              end else begin
                break;
              end
              @(cfg.vif.receiver_cb);
            end
            if (cfg.vif.get_esc() === 1'b0) cfg.vif.reset_resp();
          end else begin
            cfg.vif.wait_esc();
            @(cfg.vif.receiver_cb);
            while (cfg.vif.get_esc() === 1'b1) toggle_resp_signal();
            if (is_ping) toggle_resp_signal();
            is_ping = 0;
          end
          `uvm_info(`gfn,
              $sformatf("finished sending receiver item esc_rsp=%0b int_fail=%0b",
              req.r_esc_rsp, req.int_err), UVM_HIGH)
          seq_item_port.put_response(rsp);
        end
      join_none
    end // end forever
  endtask : rsp_escalator

  task toggle_resp_signal();
    cfg.vif.set_resp();
    @(cfg.vif.receiver_cb);
    cfg.vif.reset_resp();
    @(cfg.vif.receiver_cb);
  endtask : toggle_resp_signal

endclass : esc_receiver_driver
