// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Monitor that spots updates to the rv_dm mode pins

class rv_dm_mode_monitor extends dv_base_monitor #(.ITEM_T (rv_dm_mode_seq_item),
                                                   .CFG_T (rv_dm_mode_agent_cfg));
  `uvm_component_utils(rv_dm_mode_monitor)

  extern function new (string name, uvm_component parent);
  extern virtual task run_phase(uvm_phase phase);

  extern local function void take_snapshot();
endclass

function rv_dm_mode_monitor::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

task rv_dm_mode_monitor::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    forever begin
      @({cfg.vif.next_dm_addr, cfg.vif.lc_hw_debug_clr, cfg.vif.lc_hw_debug_en, cfg.vif.lc_dft_en,
         cfg.vif.pinmux_hw_debug_en, cfg.vif.lc_check_byp_en, cfg.vif.lc_escalate_en,
         cfg.vif.lc_init_done, cfg.vif.strap_en, cfg.vif.strap_en_override,
         cfg.vif.otp_dis_rv_dm_late_debug, cfg.vif.scanmode});
      take_snapshot();
    end
  join
endtask

function void rv_dm_mode_monitor::take_snapshot();
/// HACK  rv_dm_mode_seq_item item = rv_dm_mode_seq_item::type_id::create("item");
  rv_dm_mode_seq_item item = new;

  // As the monitor, we are filling out all the sections of the item.
  item.m_has_next_dm_addr     = 1'b1;
  item.m_has_lc_ctrl_signals  = 1'b1;
  item.m_has_pinmux_signals   = 1'b1;
  item.m_has_pwrmgr_signals   = 1'b1;
  item.m_has_otp_ctrl_signals = 1'b1;
  item.m_has_scanmode         = 1'b1;

  item.m_next_dm_addr             = cfg.vif.next_dm_addr;
  item.m_lc_hw_debug_clr          = cfg.vif.lc_hw_debug_clr;
  item.m_lc_hw_debug_en           = cfg.vif.lc_hw_debug_en;
  item.m_lc_dft_en                = cfg.vif.lc_dft_en;
  item.m_pinmux_hw_debug_en       = cfg.vif.pinmux_hw_debug_en;
  item.m_lc_check_byp_en          = cfg.vif.lc_check_byp_en;
  item.m_lc_escalate_en           = cfg.vif.lc_escalate_en;
  item.m_lc_init_done             = cfg.vif.lc_init_done;
  item.m_strap_en                 = cfg.vif.strap_en;
  item.m_strap_en_override        = cfg.vif.strap_en_override;
  item.m_otp_dis_rv_dm_late_debug = cfg.vif.otp_dis_rv_dm_late_debug;
  item.m_scanmode                 = cfg.vif.scanmode;

  analysis_port.write(item);
endfunction
