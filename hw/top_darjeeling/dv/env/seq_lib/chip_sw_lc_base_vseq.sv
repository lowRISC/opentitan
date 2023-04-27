// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is base sequence for lc_ctr chip level test.
// The purpose of the sequence is to put all redundent lc related tasks
// to common place.

class chip_sw_lc_base_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_base_vseq)
  `uvm_object_new

  // Initial lc state
  lc_ctrl_state_pkg::dec_lc_state_e init_lc_state = DecLcStInvalid;

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    `DV_GET_ENUM_PLUSARG(lc_ctrl_state_pkg::dec_lc_state_e, init_lc_state, src_dec_state)
    `uvm_info(`gfn, $sformatf("Init lc state is %0s", init_lc_state.name), UVM_MEDIUM)
    super.pre_start();
  endtask

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestLocked1 state.
    if (init_lc_state != DecLcStInvalid) begin
      cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(
          lc_ctrl_dv_utils_pkg::encode_lc_state(init_lc_state));
    end
  endfunction : backdoor_override_otp

  virtual task dut_init(string reset_kind = "HARD");
    early_cpu_init = 1;
    super.dut_init(reset_kind);

    // If init state is not reset state (DecLcStInvalid),
    // override initial lc state
    backdoor_override_otp();
  endtask

  virtual task body();
    cfg.sw_test_status_vif.set_num_iterations(num_trans);
  endtask
endclass
