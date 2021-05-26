// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests the "execute from SRAM" feature - TL transactions tagged as InstrType are
// allowed to be executed by the SRAM if configured properly.
//
// This sequence fully randomizes this configuration setting and randomly updates the configuration
// in parallel with the main sequence body.
// The scoreboard will handle all checks to ensure that transactions are dropped as necessary.
class sram_ctrl_executable_vseq extends sram_ctrl_multiple_keys_vseq;

  `uvm_object_utils(sram_ctrl_executable_vseq)
  `uvm_object_new

  bit [3:0] hw_debug_en;
  bit [7:0] en_sram_ifetch;
  bit [2:0] en_exec_csr;

  // These bits are used to create pseudo-weights for the constraint distributions
  // of the above values
  bit       is_valid;
  bit [1:0] is_off;

  virtual task pre_start();
    en_ifetch = 1;
    super.pre_start();
  endtask

  task body();
    `DV_SPINWAIT_EXIT(
        forever begin
          randomize_and_drive_ifetch_en();
          cfg.clk_rst_vif.wait_clks($urandom_range(100, 500));
        end
        ,
        super.body();
    )
  endtask

  task randomize_and_drive_ifetch_en();
    `DV_CHECK_STD_RANDOMIZE_FATAL(is_valid);
    `DV_CHECK_STD_RANDOMIZE_FATAL(is_off);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(en_exec_csr,
        // 50% chance to enable
        if (is_valid) {
          en_exec_csr == tlul_pkg::InstrEn;
        } else {
          // 75% chance to set garbage invalid data
          if (is_off == 0) {
            en_exec_csr == tlul_pkg::InstrDis;
          } else {
            !(en_exec_csr inside {tlul_pkg::InstrEn, tlul_pkg::InstrDis});
          }
        }
    )
    `uvm_info(`gfn, $sformatf("en_exec_csr: 0b%0b", en_exec_csr), UVM_HIGH)

    `DV_CHECK_STD_RANDOMIZE_FATAL(is_valid);
    `DV_CHECK_STD_RANDOMIZE_FATAL(is_off);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(en_sram_ifetch,
        // 50% chance to enable
        if (is_valid) {
          en_sram_ifetch == otp_ctrl_pkg::Enabled;
        } else {
          // 75% chance to set garbage invalid data
          if (is_off == 0) {
            en_sram_ifetch == otp_ctrl_pkg::Disabled;
          } else {
            !(en_sram_ifetch inside {otp_ctrl_pkg::Enabled, otp_ctrl_pkg::Disabled});
          }
        }
    )
    `uvm_info(`gfn, $sformatf("en_sram_ifetch: 0b%0b", en_sram_ifetch), UVM_HIGH)

    `DV_CHECK_STD_RANDOMIZE_FATAL(is_valid);
    `DV_CHECK_STD_RANDOMIZE_FATAL(is_off);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(hw_debug_en,
        // 50% chance to enable
        if (is_valid) {
          hw_debug_en == lc_ctrl_pkg::On;
        } else {
          // 75% chance to set garbage invalid data
          if (is_off == 0) {
            hw_debug_en == lc_ctrl_pkg::Off;
          } else {
            !(hw_debug_en inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off});
          }
        }
    )
    `uvm_info(`gfn, $sformatf("hw_debug_en: 0b%0b",  hw_debug_en), UVM_HIGH)

    csr_wr(ral.exec, en_exec_csr);
    cfg.exec_vif.drive_lc_hw_debug_en(hw_debug_en);
    cfg.exec_vif.drive_otp_en_sram_ifetch(en_sram_ifetch);
  endtask

endclass
