// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Driver that sends rv_dm mode updates

class rv_dm_mode_driver extends dv_base_driver #(rv_dm_mode_seq_item, rv_dm_mode_agent_cfg);
  `uvm_component_utils(rv_dm_mode_driver)

  extern function new (string name, uvm_component parent);
  extern virtual task get_and_drive();
  extern virtual task on_enter_reset();
endclass

function rv_dm_mode_driver::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task rv_dm_mode_driver::get_and_drive();
  forever begin
    rv_dm_mode_seq_item item;
    seq_item_port.get_next_item(item);

    `uvm_info("rjs", $sformatf("Setting rv_dm mode:\n%0s", item.sprint()), UVM_HIGH)

    // If we aren't in reset, drive the signals from the item (possibly through a clocking block)
    if (item.m_has_next_dm_addr) begin
      cfg.vif.next_dm_addr_internal <= item.m_next_dm_addr;
    end

    if (item.m_has_lc_ctrl_signals) begin
      cfg.vif.cb.lc_hw_debug_clr <= lc_tx_t'(item.m_lc_hw_debug_clr);
      cfg.vif.cb.lc_hw_debug_en <= lc_tx_t'(item.m_lc_hw_debug_en);
      cfg.vif.cb.lc_dft_en <= lc_tx_t'(item.m_lc_dft_en);
      cfg.vif.cb.lc_check_byp_en <= lc_tx_t'(item.m_lc_check_byp_en);
      cfg.vif.cb.lc_escalate_en <= lc_tx_t'(item.m_lc_escalate_en);
      cfg.vif.cb.lc_init_done <= lc_tx_t'(item.m_lc_init_done);
      cfg.vif.cb.strap_en_override <= item.m_strap_en_override;
    end

    if (item.m_has_pinmux_signals) begin
      cfg.vif.cb.pinmux_hw_debug_en <= lc_tx_t'(item.m_pinmux_hw_debug_en);
    end

    if (item.m_has_pwrmgr_signals) begin
      cfg.vif.strap_en_internal <= item.m_strap_en;
    end

    if (item.m_has_otp_ctrl_signals) begin
      cfg.vif.otp_dis_rv_dm_late_debug_internal <= mubi8_t'(item.m_otp_dis_rv_dm_late_debug);
    end

    if (item.m_has_scanmode) begin
      cfg.vif.scanmode_internal <= mubi4_t'(item.m_scanmode);
    end

    seq_item_port.item_done(item);
  end
endtask

task rv_dm_mode_driver::on_enter_reset();
  // Nothing to do for this driver: there isn't actually a reset on the interface.
endtask
