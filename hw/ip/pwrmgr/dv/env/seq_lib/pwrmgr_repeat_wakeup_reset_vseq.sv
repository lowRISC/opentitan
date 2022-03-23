// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// The wakeup_reset test randomly enables wakeups and resets, info capture, and interrupts,
// and sends wakeups and resets in close temporal proximity at random times.
class pwrmgr_repeat_wakeup_reset_vseq extends pwrmgr_wakeup_reset_vseq;
  `uvm_object_utils(pwrmgr_repeat_wakeup_reset_vseq)

  `uvm_object_new

  bit[lc_ctrl_pkg::TxWidth-1:0] bad_lc_tx;

  // add invalid value to rom_ctrl
  virtual task twirl_rom_response();
    add_rom_rsp_noise();
    cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4False;
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
    cfg.clk_rst_vif.wait_clks(5);
    add_rom_rsp_noise();
    wait(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheck);
    add_rom_rsp_noise();
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
    cfg.clk_rst_vif.wait_clks(5);
    cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
  endtask

  function bit[lc_ctrl_pkg::TxWidth-1:0] get_lc_ctrl();
    randcase
      1: get_lc_ctrl = lc_ctrl_pkg::On;
      1: get_lc_ctrl = lc_ctrl_pkg::Off;
      2: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(get_lc_ctrl,
                                            get_lc_ctrl != lc_ctrl_pkg::On &&
                                            get_lc_ctrl != lc_ctrl_pkg::Off;)
    endcase
  endfunction // get_lc_ctrl

  task body();
    num_trans_c.constraint_mode(0);
    num_trans = 50;

    disable_assert(mubi_mode);
    fork
      super.body();
      drv_stim(mubi_mode);
    join
  endtask // body

  function void disable_assert(pwrmgr_mubi_e mubi_mode);
    if (mubi_mode == PwrmgrMubiRomCtrl) begin
      $assertoff(0, "tb.dut.u_cdc.u_sync_rom_ctrl");
    end
  endfunction // disable_assert

  task drv_stim(pwrmgr_mubi_e mubi_mode);
    if (mubi_mode == PwrmgrMubiLcCtrl) drv_lc_ctrl();
  endtask // drv_stim

  task drv_lc_ctrl();
    int delay;

    repeat(50) begin
      cfg.pwrmgr_vif.lc_hw_debug_en = get_lc_ctrl();
      delay = $urandom_range(5,20);
      #(delay * 1us);
      cfg.pwrmgr_vif.lc_dft_en = get_lc_ctrl();
      delay = $urandom_range(5,20);
      #(delay * 1us);
    end
  endtask // drv_lc_ctrl

endclass : pwrmgr_repeat_wakeup_reset_vseq
