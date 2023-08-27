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
    fork
      begin : first_isolation_fork
        foreach (cfg.pwrmgr_vif.rom_ctrl[k]) begin : rom_ctrls
          fork
            automatic int i = k;
            begin
              automatic bit [3:0] wait1;
              `DV_CHECK_STD_RANDOMIZE_FATAL(wait1)
              cfg.pwrmgr_vif.rom_ctrl[i].done = prim_mubi_pkg::MuBi4False;
              cfg.pwrmgr_vif.rom_ctrl[i].good = prim_mubi_pkg::MuBi4False;
              cfg.clk_rst_vif.wait_clks(wait1);
            end
          join_none
        end : rom_ctrls
        wait fork;
      end : first_isolation_fork
    join
    add_rom_rsp_noise();
    wait(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone);
    add_rom_rsp_noise();
    fork
      begin : second_isolation_fork
        foreach (cfg.pwrmgr_vif.rom_ctrl[k]) begin : rom_ctrls
          fork
            automatic int i = k;
            begin
              automatic bit [3:0] wait2;
              `DV_CHECK_STD_RANDOMIZE_FATAL(wait2)
              cfg.pwrmgr_vif.rom_ctrl[i].good = prim_mubi_pkg::MuBi4True;
              cfg.clk_rst_vif.wait_clks(wait2);
              cfg.pwrmgr_vif.rom_ctrl[i].done = prim_mubi_pkg::MuBi4True;
            end
          join_none
        end : rom_ctrls
        wait fork;
      end : second_isolation_fork
    join
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

  // This function is cumbersome because $asserton/off take literal strings, so we cannot use
  // $sformatf to create the individual scope strings. It supports up to 3 rom inputs, if more
  // are needed, extend it.
  // Better yet, if you find a way to make this cleaner, go ahead.
  function void disable_assert();
    int rom_ins = pwrmgr_reg_pkg::NumRomInputs;
    `DV_CHECK_LE(pwrmgr_reg_pkg::NumRomInputs, 3, "Extend support for more rom inputs here")
    $assertoff(0, "tb.dut.u_cdc.gen_rom_inputs[0].u_sync_rom_ctrl");
    if (rom_ins > 1) $assertoff(0, "tb.dut.u_cdc.gen_rom_inputs[1].u_sync_rom_ctrl");
    if (rom_ins > 2) $assertoff(0, "tb.dut.u_cdc.gen_rom_inputs[2].u_sync_rom_ctrl");
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
