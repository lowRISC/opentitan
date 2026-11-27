// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drive the inputs to keymgr_dpe. The keymgr_dpe_base_seq randomizes the input items and sends them
// to the driver via the sequencer. The sequence is started once in keymgr_dpe_base_vseq.
class keymgr_dpe_driver extends dv_base_driver #(.ITEM_T(keymgr_dpe_seq_item),
                                                 .CFG_T(keymgr_dpe_agent_cfg));

  `uvm_component_utils(keymgr_dpe_driver)

  extern function new(string name, uvm_component parent);
  extern local task drive_item(ITEM_T item);
  extern virtual task reset_signals();
  extern virtual task get_and_drive();
endclass

function keymgr_dpe_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

task keymgr_dpe_driver::reset_signals();
  forever begin
    // Wait for reset.
    wait(cfg.in_reset);

    cfg.m_vif.lc_keymgr_en_internal       <= lc_ctrl_pkg::LC_TX_DEFAULT;
    cfg.m_vif.lc_keymgr_div_internal      <= lc_keymgr_div_t'('0);
    cfg.m_vif.creator_root_key_internal   <= KEYMGR_DPE_CREATOR_ROOT_KEY_DEFAULT;
    cfg.m_vif.secondary_root_key_internal <= KEYMGR_DPE_SECONDARY_ROOT_KEY_DEFAULT;
    cfg.m_vif.creator_seed_internal       <= KEYMGR_DPE_CREATOR_SEED_DEFAULT;
    cfg.m_vif.owner_seed_internal         <= KEYMGR_DPE_OWNER_SEED_DEFAULT;
    cfg.m_vif.device_id_internal          <= keymgr_dpe_device_id_t'('0);
    cfg.m_vif.field_entropy_internal      <= KEYMGR_DPE_FIELD_ENTROPY_DEFAULT;
    cfg.m_vif.rom_digest_internal         <= '{default : 0};

    wait(!cfg.in_reset);
  end
endtask

task keymgr_dpe_driver::drive_item(ITEM_T item);
  if (item == null) `uvm_fatal(`gfn, "Received null item to drive!");

  if (cfg.in_reset) return;

  // Drive all the inputs to keymgr_dpe. They are quasi-static so no need to drive them on an edge
  // of a clocking block.
  cfg.m_vif.lc_keymgr_en_internal       <= item.m_lc_keymgr_en;
  cfg.m_vif.lc_keymgr_div_internal      <= item.m_lc_keymgr_div;
  cfg.m_vif.creator_root_key_internal   <= item.m_root_key;
  cfg.m_vif.secondary_root_key_internal <= item.m_secondary_root_key;
  cfg.m_vif.creator_seed_internal       <= item.m_creator_seed;
  cfg.m_vif.owner_seed_internal         <= item.m_owner_seed;
  cfg.m_vif.device_id_internal          <= item.m_device_id;
  cfg.m_vif.field_entropy_internal      <= item.m_field_entropy;
  cfg.m_vif.rom_digest_internal         <= item.m_rom_digest;
endtask

task keymgr_dpe_driver::get_and_drive();
  ITEM_T item;
  forever begin
    seq_item_port.get_next_item(item);
    drive_item(item);
    seq_item_port.item_done();
  end
endtask
