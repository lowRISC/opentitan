// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_handler receiver driver
// ---------------------------------------------
class esc_receiver_driver extends alert_esc_base_driver;

  `uvm_component_utils(esc_receiver_driver)

  `uvm_component_new

  virtual task reset_signals();
    cfg.vif.reset_resp();
  endtask

  virtual task drive_req();
    fork
      rsp_escalator();
    join_none
  endtask : drive_req

  virtual task rsp_escalator();
    forever begin
      alert_esc_seq_item req, rsp;
      wait(r_esc_rsp_q.size() > 0);
      req = r_esc_rsp_q.pop_front();
      $cast(rsp, req.clone());
      rsp.set_id_info(req);
      `uvm_info(`gfn,
          $sformatf("starting to send receiver item, esc_rsp=%0b, int_fail=%0b",
          req.r_esc_rsp, req.int_err), UVM_HIGH)

      cfg.vif.wait_esc();
      @(cfg.vif.receiver_cb);
      while (cfg.vif.receiver_cb.esc_tx.esc_p === 1'b1) begin
        cfg.vif.set_resp();
        @(cfg.vif.receiver_cb);
        cfg.vif.reset_resp();
        @(cfg.vif.receiver_cb);
      end

      `uvm_info(`gfn,
          $sformatf("finished sending receiver item, esc_rsp=%0b, int_fail=%0b",
          req.r_esc_rsp, req.int_err), UVM_HIGH)
      seq_item_port.put_response(rsp);
    end
  endtask : rsp_escalator
endclass : esc_receiver_driver
