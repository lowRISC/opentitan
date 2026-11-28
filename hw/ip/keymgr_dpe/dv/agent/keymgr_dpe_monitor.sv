// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Monitors the keymgr_dpe interface and broadcasts the sampled values to the other components via
// the analysis ports.
class keymgr_dpe_monitor extends dv_base_monitor #(.ITEM_T (keymgr_dpe_seq_item),
                                                   .CFG_T  (keymgr_dpe_agent_cfg));

  `uvm_component_utils(keymgr_dpe_monitor)

  // Broadcast the inputs to the scoreboard.
  uvm_analysis_port #(ITEM_T) m_hw_inputs_ap;

  // Broadcast the HW sideload keys to the scoreboard.
  uvm_analysis_port #(ITEM_T) m_sideload_ports_ap;

  extern function new(string name, uvm_component parent);
  extern local task sample_hw_inputs();
  extern local task sample_sideload_ports();
  extern local task monitor_reset();
  extern virtual task run_phase(uvm_phase phase);
endclass : keymgr_dpe_monitor

function keymgr_dpe_monitor::new(string name, uvm_component parent);
  super.new(name, parent);
  m_hw_inputs_ap      = new("m_hw_inputs_ap", this);
  m_sideload_ports_ap = new("m_sideload_ports_ap", this);
endfunction

task keymgr_dpe_monitor::sample_hw_inputs();
  forever begin
    ITEM_T item;

    // Wait until any of the inputs changes.
    @(cfg.m_vif.mon_cb.lc_keymgr_en       or
      cfg.m_vif.mon_cb.lc_keymgr_div      or
      cfg.m_vif.mon_cb.creator_root_key   or
      cfg.m_vif.mon_cb.secondary_root_key or
      cfg.m_vif.mon_cb.creator_seed       or
      cfg.m_vif.mon_cb.owner_seed         or
      cfg.m_vif.mon_cb.device_id          or
      cfg.m_vif.mon_cb.field_entropy      or
      cfg.m_vif.mon_cb.rom_digest);

    item = keymgr_dpe_seq_item::type_id::create("item");

    // Something has changed; sample it now and broadcast it via the m_hw_inputs_ap.
    item.m_lc_keymgr_en       = cfg.m_vif.mon_cb.lc_keymgr_en;
    item.m_lc_keymgr_div      = cfg.m_vif.mon_cb.lc_keymgr_div;
    item.m_root_key           = cfg.m_vif.mon_cb.creator_root_key;
    item.m_secondary_root_key = cfg.m_vif.mon_cb.secondary_root_key;
    item.m_creator_seed       = cfg.m_vif.mon_cb.creator_seed;
    item.m_owner_seed         = cfg.m_vif.mon_cb.owner_seed;
    item.m_device_id          = cfg.m_vif.mon_cb.device_id;
    item.m_field_entropy      = cfg.m_vif.mon_cb.field_entropy;
    item.m_rom_digest         = cfg.m_vif.mon_cb.rom_digest;

    if (!cfg.in_reset) m_hw_inputs_ap.write(item);
  end
endtask

task keymgr_dpe_monitor::sample_sideload_ports();
  forever begin
    ITEM_T item;

    // Wait until any of the sideload outputs changes.
    @(cfg.m_vif.mon_cb.aes_key  or
      cfg.m_vif.mon_cb.kmac_key or
      cfg.m_vif.mon_cb.hmac_key or
      cfg.m_vif.mon_cb.otbn_key);

    item = keymgr_dpe_seq_item::type_id::create("item");

    // Something has changed; sample it now and broadcast it via the m_sideload_ports_ap.
    item.m_aes_key  = cfg.m_vif.mon_cb.aes_key;
    item.m_kmac_key = cfg.m_vif.mon_cb.kmac_key;
    item.m_hmac_key = cfg.m_vif.mon_cb.hmac_key;
    item.m_otbn_key = cfg.m_vif.mon_cb.otbn_key;

    if (!cfg.in_reset) m_sideload_ports_ap.write(item);
  end
endtask

task keymgr_dpe_monitor::monitor_reset();
  forever begin
    wait(!cfg.m_vif.rst_ni);
    cfg.in_reset = 1;
    wait(cfg.m_vif.rst_ni);
    cfg.in_reset = 0;
  end
endtask

task keymgr_dpe_monitor::run_phase(uvm_phase phase);
  super.run_phase(phase);
  fork
    sample_hw_inputs();
    sample_sideload_ports();
    monitor_reset();
  join_none
endtask
