// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// The wakeup_reset test randomly enables wakeups and resets, info capture, and interrupts,
// and sends wakeups and resets in close temporal proximity at random times.
class pwrmgr_repeat_wakeup_reset_vseq extends pwrmgr_wakeup_reset_vseq;
  `uvm_object_utils(pwrmgr_repeat_wakeup_reset_vseq)

  `uvm_object_new

  bit [lc_ctrl_pkg::TxWidth-1:0] bad_lc_tx;

  bit super_sequence_done;

  task body();
    num_trans_c.constraint_mode(0);
    num_trans = 50;
    super_sequence_done = 0;

    control_rom_ctrl_sync_assertions(.enable(1'b0));
    fork
      begin
        super.body();
        super_sequence_done = 1;
      end
      drv_stim();
    join
  endtask : body

  task drv_stim();
    int unsigned cycles_from_reset = $urandom_range(2, 8);
    int unsigned micros_to_release = $urandom_range(2, 4);

    repeat (50) begin : repeat_50
      wait(cfg.esc_clk_rst_vif.rst_n);
      cfg.clk_rst_vif.wait_clks(cycles_from_reset);
      if (super_sequence_done) break;

      drive_inputs(1);
      #(micros_to_release * 1us);
      if (super_sequence_done) break;

      drive_inputs(0);
      #(micros_to_release * 1us);
    end : repeat_50
    `uvm_info(`gfn, "ended drv_stim", UVM_MEDIUM)
  endtask : drv_stim

  task drive_inputs(bit phase0);
    case (mubi_mode)
      PwrmgrMubiLcCtrl:  drive_lc_ctrl_inputs(phase0);
      PwrmgrMubiRomCtrl: drive_rom_ctrl_inputs(phase0);
      default: `uvm_fatal(get_full_name(), $sformatf("Unknown mubi_mode: %s", mubi_mode.name()))
    endcase
  endtask : drive_inputs

  task drive_rom_ctrl_inputs(bit phase0);
    if (phase0) begin
      for (int r = 0; r < NumRomInputs; r++) begin
        mubi4_t rand_done = get_rand_mubi4_val(.t_weight(1), .f_weight(1), .other_weight(2));
        mubi4_t rand_good = get_rand_mubi4_val(.t_weight(1), .f_weight(1), .other_weight(2));
        `uvm_info(`gfn, $sformatf("Injection to rom_ctrl[%0d]", r), UVM_MEDIUM)
        cfg.pwrmgr_vif.update_rom_ctrl('{done: rand_done, good: rand_good}, r);
      end
    end else begin
      update_roms_response(.done(MuBi4True), .good(MuBi4True));
    end
  endtask : drive_rom_ctrl_inputs

  task drive_lc_ctrl_inputs(bit phase0);
    if (phase0) begin
      cfg.pwrmgr_vif.lc_hw_debug_en = get_rand_lc_tx_val(.t_weight(1),
                                                         .f_weight(1),
                                                         .other_weight(2));
    end else begin
      cfg.pwrmgr_vif.lc_dft_en = get_rand_lc_tx_val(.t_weight(1), .f_weight(1), .other_weight(2));
    end
  endtask : drive_lc_ctrl_inputs

endclass : pwrmgr_repeat_wakeup_reset_vseq
