// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Report catcher/demoter for lc_ctrl TB
class lc_ctrl_report_catcher extends uvm_report_catcher;

  protected uvm_severity m_changed_sev[string][string];

  `uvm_object_utils(lc_ctrl_report_catcher)
  `uvm_object_new

  // Called for all messages
  virtual function action_e catch();
    string id = get_id();
    if (m_changed_sev.exists(id)) begin
      foreach(m_changed_sev[id][msg]) begin
        if (uvm_re_match(msg, get_message())) begin
          set_severity(m_changed_sev[id][msg]);
        end
      end
    end
    return THROW;
  endfunction

  // Change severity of a message
  virtual function void add_change_sev(string id, string msg, uvm_severity sev);
    m_changed_sev[id][msg] = sev;
  endfunction

  // Remove a change
  virtual function void remove_change_sev(string id, string msg="");
    if(m_changed_sev.exists(id))
      if (msg == "") begin
        // Delete all with id if message is blank
        m_changed_sev.delete(id);
      end else if (m_changed_sev[id].exists(msg)) begin
        m_changed_sev[id].delete(msg);
      end
  endfunction


endclass