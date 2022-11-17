// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class chip_sw_lc_ctrl_scrap_vseq extends chip_sw_base_vseq;
  import lc_ctrl_state_pkg::dec_lc_state_e;
  import lc_ctrl_state_pkg::lc_state_e;
  import lc_ctrl_dv_utils_pkg::encode_lc_state;

  `uvm_object_utils(chip_sw_lc_ctrl_scrap_vseq)

  `uvm_object_new

  rand dec_lc_state_e src_state;
  constraint valid_src_state_c {
    !(src_state inside {DecLcStScrap, DecLcStInvalid, DecLcStPostTrans, DecLcStEscalate});
  }

  function void post_randomize();
    super.post_randomize();
    // source state is randomized, but if a plusarg is supplied, assign the given value
    `DV_GET_ENUM_PLUSARG(lc_ctrl_state_pkg::dec_lc_state_e, src_state, src_dec_state)
    `uvm_info(`gfn, $sformatf("Source state is %0s", src_state.name), UVM_MEDIUM)

    // a guard to check we didn't screw up
    `DV_CHECK_FATAL(src_state != DecLcStScrap)
  endfunction : post_randomize

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask : pre_start

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestLocked1 state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(encode_lc_state(src_state));
  endfunction : backdoor_override_otp

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    backdoor_override_otp();
  endtask : dut_init

  virtual task body();
    bit [BUS_DW-1:0] state;
    super.body();

    // Wait for LC_CTRL post initialization
    wait_lc_ready(.allow_err(1));

    // perform a LC state transition to SCRAP
    jtag_lc_state_transition(src_state, DecLcStScrap);

    // LC state transition requires a chip reset.
    `uvm_info(`gfn, $sformatf("Applying reset after lc transition from %s state", src_state.name),
              UVM_MEDIUM)
    apply_reset();

    wait_lc_initialized(.allow_err(1));

    // check LC state is indeed in SCRAP
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h, state);
    `DV_CHECK_EQ(state, {DecLcStateNumRep{DecLcStScrap}})
  endtask : body

  task post_start();
    // once in SCRAP mode, the CPU can't execute any SW code, so
    // we don't expect the SW to be done
    // so we shutdown the device, and then override the test exit from here
    override_test_status_and_finish(.passed(1));

    super.post_start();
  endtask : post_start
endclass : chip_sw_lc_ctrl_scrap_vseq
