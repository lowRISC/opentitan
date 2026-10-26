// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Check that no key survives a fault on the way to the Invalid state:
// 1. A fault during the first advance must stop the root key from being loaded into a slot.
// 2. A fault in the Disabled state must move to Invalid and wipe the sideload keys.
// The scoreboard only models faults reported at the end of an operation, so it is disabled.
class keymgr_dpe_fault_wipe_vseq extends keymgr_dpe_base_vseq;
  `uvm_object_utils(keymgr_dpe_fault_wipe_vseq)
  `uvm_object_new

  rand keymgr_dpe_pkg::keymgr_dpe_working_state_e adv_fault_state;

  constraint adv_fault_state_c {
    adv_fault_state inside {
      keymgr_dpe_pkg::StCtrlDpeEntropyReseed,
      keymgr_dpe_pkg::StCtrlDpeRandom,
      keymgr_dpe_pkg::StCtrlDpeRootKey
    };
  }

  virtual task pre_start();
    cfg.en_scb = 0;
    cfg.keymgr_dpe_vif.en_chk = 0;
    expect_fatal_alerts = 1;
    super.pre_start();
  endtask

  task body();
    bit disabled_first = $urandom_range(0, 1);

    for (int i = 0; i < 2; i++) begin
      if (i > 0) begin
        dut_init("HARD");
        current_state = keymgr_dpe_pkg::StWorkDpeReset;
      end
      if (disabled_first ^ (i > 0)) fault_in_disabled();
      else                          fault_during_first_advance();
    end
  endtask : body

  task fault_during_first_advance();
    keymgr_dpe_pkg::keymgr_dpe_slot_t [keymgr_dpe_env_pkg::DvNumInstHwSlot-1:0] loaded_slots;
    bit [keymgr_dpe_pkg::KeyWidth-1:0] root_key;

    root_key = cfg.keymgr_dpe_vif.creator_root_key.share0 ^
               cfg.keymgr_dpe_vif.creator_root_key.share1;
    src_slot = 0;
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(dst_slot, dst_slot < keymgr_dpe_env_pkg::DvNumInstHwSlot;)
    keymgr_dpe_advance(.wait_done(0));
    fork
      cfg.keymgr_dpe_vif.get_slots_after_root_key(loaded_slots);
      begin
        cfg.keymgr_dpe_vif.inject_regfile_intg_err(adv_fault_state);
        // Start the check before the first alert, so it follows the alert handshakes in phase.
        check_fatal_alert_nonblocking("fatal_fault_err");
      end
    join

    csr_spinwait(.ptr(ral.op_status.status), .exp_data(keymgr_dpe_pkg::OpWip),
                 .compare_op(CompareOpNe));
    csr_rd_check(.ptr(ral.op_status.status), .compare_value(keymgr_dpe_pkg::OpDoneFail));
    csr_rd_check(.ptr(ral.start.en), .compare_value(0));
    csr_rd_check(.ptr(ral.intr_state.op_done), .compare_value(1));
    csr_rd_check(.ptr(ral.err_code.invalid_op), .compare_value(1));
    csr_rd_check(.ptr(ral.fault_status.regfile_intg), .compare_value(1));
    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_dpe_pkg::StWorkDpeInvalid));
    // The root key must not be loaded in the root key cycle, nor appear in a slot afterwards.
    `DV_CHECK_NE(root_key, 0)
    for (int i = 0; i < keymgr_dpe_env_pkg::DvNumInstHwSlot; i++) begin
      `DV_CHECK_EQ(loaded_slots[i].valid, 0,
                   $sformatf("slot %0d loaded despite a fault in %s", i, adv_fault_state.name))
      `DV_CHECK_NE(unmask(loaded_slots[i].key), root_key,
                   $sformatf("slot %0d loaded despite a fault in %s", i, adv_fault_state.name))
      `DV_CHECK_EQ(cfg.keymgr_dpe_vif.internal_key_slots[i].valid, 0,
                   $sformatf("slot %0d after a fault in %s", i, adv_fault_state.name))
      `DV_CHECK_NE(unmask(cfg.keymgr_dpe_vif.internal_key_slots[i].key), root_key,
                   $sformatf("slot %0d after a fault in %s", i, adv_fault_state.name))
    end
    wait_fatal_alert();
  endtask

  task fault_in_disabled();
    bit [keymgr_dpe_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_before, sw_after;
    keymgr_dpe_pkg::hw_key_req_t aes_before;
    kmac_pkg::rsp_digest_t sw_digest;

    // Latch the root key, then advance with a policy that allows key generation. The root key
    // policy does not retain the parent, so the advance must stay in the same slot.
    src_slot = 0;
    dst_slot = 0;
    keymgr_dpe_advance();
    policy = '{allow_keygen: 1, retain_parent: 0, exportable: 0, allow_child: 1};
    keymgr_dpe_advance();
    keymgr_dpe_generate(.operation(keymgr_dpe_pkg::OpDpeGenHwOut), .key_dest(keymgr_dpe_pkg::Aes),
                        .key_version(0));
    `DV_CHECK_EQ(cfg.keymgr_dpe_vif.aes_key.valid, 1)
    // Reading the software output clears it. The KMAC model returns a random digest unless it is
    // given one, so generate the software key twice from the same digest: the second time, the key
    // that was read is held in the registers, unread, when the fault arrives.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(sw_digest,
                                       !(sw_digest.digest_share0 inside {'0, '1});
                                       !(sw_digest.digest_share1 inside {'0, '1});)
    for (int i = 0; i < 2; i++) begin
      cfg.m_kmac_agent_cfg.add_user_digest(sw_digest);
      keymgr_dpe_generate(.operation(keymgr_dpe_pkg::OpDpeGenSwOut),
                          .key_dest(keymgr_dpe_pkg::None), .key_version(0));
      if (i == 0) read_sw_shares(sw_before);
    end

    // Disabling keeps the sideload keys.
    keymgr_dpe_disable(.num_gen_op(0), .num_adv_op(0));
    `DV_CHECK_EQ(current_state, keymgr_dpe_pkg::StWorkDpeDisabled)
    `DV_CHECK_EQ(cfg.keymgr_dpe_vif.aes_key.valid, 1)
    aes_before = cfg.keymgr_dpe_vif.aes_key;
    // A fault with no operation running must not report a completion.
    csr_wr(.ptr(ral.intr_state), .value('1));

    cfg.clk_rst_vif.wait_clks($urandom_range(0, 100));
    cfg.keymgr_dpe_vif.inject_regfile_intg_err(keymgr_dpe_pkg::StCtrlDpeDisabled);
    check_fatal_alert_nonblocking("fatal_fault_err");
    cfg.clk_rst_vif.wait_clks(10);

    csr_rd_check(.ptr(ral.working_state), .compare_value(keymgr_dpe_pkg::StWorkDpeInvalid));
    csr_rd_check(.ptr(ral.fault_status.regfile_intg), .compare_value(1));
    csr_rd_check(.ptr(ral.start.en), .compare_value(0));
    csr_rd_check(.ptr(ral.intr_state), .compare_value(0));
    `DV_CHECK_EQ(cfg.keymgr_dpe_vif.aes_key.valid, 0)
    check_wiped(aes_before.key, cfg.keymgr_dpe_vif.aes_key.key, "AES key");
    read_sw_shares(sw_after);
    check_wiped(sw_before, sw_after, "software output");
    wait_fatal_alert();
  endtask

  // Wait until the fatal alert has fired, so the reset before the next scenario cannot cancel its
  // check.
  task wait_fatal_alert();
    `DV_SPINWAIT(
        while (!cfg.m_alert_agent_cfgs["fatal_fault_err"].vif.get_alert()) begin
          cfg.clk_rst_vif.wait_clks(1);
        end,
        "fatal_fault_err did not fire")
    `DV_SPINWAIT(cfg.m_alert_agent_cfgs["fatal_fault_err"].vif.wait_ack_complete();,
                 "fatal_fault_err handshake did not complete")
  endtask

  function bit [keymgr_dpe_pkg::KeyWidth-1:0] unmask(
      bit [keymgr_dpe_pkg::Shares-1:0][keymgr_dpe_pkg::KeyWidth-1:0] key);
    return key[0] ^ key[1];
  endfunction

  // Check that every word of the unmasked key differs from its value before the wipe.
  function void check_wiped(bit [keymgr_dpe_pkg::Shares-1:0][keymgr_dpe_pkg::KeyWidth-1:0] old_key,
                            bit [keymgr_dpe_pkg::Shares-1:0][keymgr_dpe_pkg::KeyWidth-1:0] new_key,
                            string name);
    bit [keymgr_dpe_pkg::KeyWidth/TL_DW-1:0][TL_DW-1:0] key_before = old_key[0] ^ old_key[1];
    bit [keymgr_dpe_pkg::KeyWidth/TL_DW-1:0][TL_DW-1:0] key_after = new_key[0] ^ new_key[1];
    foreach (key_after[i]) begin
      `DV_CHECK_NE(key_after[i], key_before[i], $sformatf("%s word %0d not wiped", name, i))
    end
  endfunction

  // Without the scoreboard, reads do not update the RAL mirror, so only the checks in this
  // sequence are used.
  virtual function bit get_check_en();
    return 0;
  endfunction
endclass : keymgr_dpe_fault_wipe_vseq
