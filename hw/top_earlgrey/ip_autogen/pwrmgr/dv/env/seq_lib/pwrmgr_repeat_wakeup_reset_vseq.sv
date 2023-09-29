// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// The wakeup_reset test randomly enables wakeups and resets, info capture, and interrupts,
// and sends wakeups and resets in close temporal proximity at random times.
class pwrmgr_repeat_wakeup_reset_vseq extends pwrmgr_wakeup_reset_vseq;
  `uvm_object_utils(pwrmgr_repeat_wakeup_reset_vseq)

  `uvm_object_new

  bit [lc_ctrl_pkg::TxWidth-1:0] bad_lc_tx;

  int cycles_from_reset;
  int micros_to_release;

  bit super_sequence_done;

  // add invalid value to rom_ctrl
  virtual task twirl_rom_response();
    add_rom_rsp_noise();
    cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4False;
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
    cfg.clk_rst_vif.wait_clks(5);
    add_rom_rsp_noise();
    wait(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone);
    add_rom_rsp_noise();
    cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
    cfg.clk_rst_vif.wait_clks(5);
    cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
  endtask

  task body();
    num_trans_c.constraint_mode(0);
    num_trans = 50;
    super_sequence_done = 0;

    disable_assert();
    fork
      begin
        super.body();
        super_sequence_done = 1;
      end
      drv_stim(mubi_mode);
    join
  endtask : body

  function void disable_assert();
    $assertoff(0, "tb.dut.u_cdc.u_sync_rom_ctrl");
  endfunction : disable_assert

  task drv_stim(pwrmgr_mubi_e mubi_mode);
    if (mubi_mode == PwrmgrMubiLcCtrl) drv_lc_ctrl();
  endtask : drv_stim

  task drv_lc_ctrl();
    int delay;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cycles_from_reset, cycles_from_reset inside {[2 : 8]};)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(micros_to_release, micros_to_release inside {[2 : 4]};)

    repeat (50) begin
      wait(cfg.esc_clk_rst_vif.rst_n);
      cfg.clk_rst_vif.wait_clks(cycles_from_reset);
      if (super_sequence_done) break;
      `uvm_info(`gfn, "Injection to lc_hw_debug_en", UVM_MEDIUM)
      cfg.pwrmgr_vif.lc_hw_debug_en = get_rand_lc_tx_val(
          .t_weight(1), .f_weight(1), .other_weight(2)
      );
      #(micros_to_release * 1us);
      `uvm_info(`gfn, "Injection to lc_dft_en", UVM_MEDIUM)
      if (super_sequence_done) break;
      cfg.pwrmgr_vif.lc_dft_en = get_rand_lc_tx_val(.t_weight(1), .f_weight(1), .other_weight(2));
      #(micros_to_release * 1us);
    end  // repeat (50)
    `uvm_info(`gfn, "ended drv_lc_ctrl", UVM_MEDIUM)
  endtask : drv_lc_ctrl

endclass : pwrmgr_repeat_wakeup_reset_vseq
