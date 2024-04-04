// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// ---------------------------------------------
// Alert_esc_base driver
// ---------------------------------------------
class alert_esc_base_driver extends dv_base_driver#(alert_esc_seq_item, alert_esc_agent_cfg);
  alert_esc_seq_item r_alert_ping_send_q[$], r_alert_rsp_q[$], r_esc_rsp_q[$],
                     s_alert_send_q[$], s_alert_ping_rsp_q[$];

  `uvm_component_utils(alert_esc_base_driver)

  `uvm_component_new

  // drive trans received from sequencer
  virtual task get_and_drive();
    fork
      get_req();
      drive_req();
    join_none
  endtask

  virtual task drive_req();
    `uvm_fatal(`gfn, "this is implemented as pure virtual task - please extend")
  endtask

  virtual task get_req();
    @(posedge cfg.vif.rst_n);
    forever begin
      alert_esc_seq_item req_clone;
      seq_item_port.get(req);
      `downcast(req_clone, req.clone());
      req_clone.set_id_info(req);
      // receiver mode
      if (req.r_alert_ping_send) r_alert_ping_send_q.push_back(req_clone);
      if (req.r_alert_rsp)       r_alert_rsp_q.push_back(req_clone);
      if (req.r_esc_rsp)         r_esc_rsp_q.push_back(req_clone);
      // sender mode
      if (req.s_alert_send)      s_alert_send_q.push_back(req_clone);
      if (req.s_alert_ping_rsp)  s_alert_ping_rsp_q.push_back(req_clone);
    end
  endtask : get_req

endclass
