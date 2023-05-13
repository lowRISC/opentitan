// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This open source vendor_test partition status will always return 0 because the generic_otp ties
// the status to 0.
// For close source testing, it is recommended to expand this sequence to check
// otp_vendor_test_status register value under different LC states.
class chip_sw_otp_ctrl_vendor_test_csr_access_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_otp_ctrl_vendor_test_csr_access_vseq)

  `uvm_object_new

  rand lc_state_e      lc_state;
  rand bit [TL_DW-1:0] w_data;
  bit [TL_DW-1:0] otp_vendor_test_status;

  constraint lc_state_c {
    lc_state dist {
        LcStRaw :/ 1,
        [LcStTestUnlocked0 : LcStTestUnlocked7] :/ 4,
        LcStDev :/ 1,
        LcStProd :/ 1,
        LcStProdEnd :/ 1,
        LcStRma :/ 1
    };
  }

  virtual task pre_start();
    // Select lc jtag
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual function void backdoor_override_otp();
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(lc_state);
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    backdoor_override_otp();
  endtask

  virtual task body();
    super.body();

    // Before issuing jtag access (from wait_lc_ready),
    // make sure lc_ctrl readya by polling csr.
    wait_rom_check_done();
    wait_lc_ready(.allow_err(1));

    // Claim the mux interface via JTAG.
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.claim_transition_if.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         prim_mubi_pkg::MuBi8True);

    // Write random value to the otp_vendor_test_ctrl register.
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl.otp_vendor_test_ctrl.get_offset(),
                                         p_sequencer.jtag_sequencer_h, w_data);

    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.otp_vendor_test_status.get_offset(),
                                        p_sequencer.jtag_sequencer_h, otp_vendor_test_status);

    check_otp_vendor_test_status();
  endtask

  virtual task check_otp_vendor_test_status();
    logic [TL_DW-1:0] vendor_test_ctrl =
                      cfg.chip_vif.signal_probe_otp_vendor_test_ctrl(SignalProbeSample);

    // In open source prim_otp module, the vendor_test_status output is tied to 0.
    `DV_CHECK_EQ(otp_vendor_test_status, 0)

    // Probe vendor_test_ctrl from OTP_CTRL port to ensure that in certain lc states, the
    // vendor_test_req is not gated.
    if (lc_state inside {LcStRaw, [LcStTestUnlocked0 : LcStTestUnlocked7], LcStRma}) begin
      `DV_CHECK_EQ(vendor_test_ctrl, w_data);
    end else begin
      `DV_CHECK_EQ(vendor_test_ctrl, 0);
    end
  endtask

  task post_start();
    // Some LC state does not enable CPU so sw cannot return a pass status.
    override_test_status_and_finish(.passed(1));

    super.post_start();
  endtask : post_start

endclass
