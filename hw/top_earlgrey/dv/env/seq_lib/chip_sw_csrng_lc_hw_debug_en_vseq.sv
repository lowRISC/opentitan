// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class is used for the test `chip_sw_csrng_lc_hw_debug_en_vseq_test.
// Please refer to the testplan for more details regarding the OTP
// initialization values.
class chip_sw_csrng_lc_hw_debug_en_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_csrng_lc_hw_debug_en_vseq)

  `uvm_object_new

  localparam string LC_CTRL_TRANS_SUCCESS_PATH =
    "tb.dut.top_earlgrey.u_lc_ctrl.u_lc_ctrl_fsm.trans_success_o";

  localparam logic [255:0] DEVICE_ID =
      256'hFA53B8058E157CB69F1F413E87242971B6B52A656A1CAB7FEBF21E5BF1F45EDD;
  localparam logic [255:0] MANUF_STATE =
      256'h41389646B3968A3B128F4AF0AFFC1AAC77ADEFF42376E09D523D5C06786AAC34;
  localparam logic [7:0] MUBI8TRUE = prim_mubi_pkg::MuBi8True;
  localparam logic [7:0] MUBI8FALSE = prim_mubi_pkg::MuBi8False;

  // When the test exit transition has been completed the CPU will be disabled
  // and therefore it cannot be detected in SW. Detect this transition here
  // to allow the CPU to be reset.
  virtual task wait_for_transition();
    int retval;
    int transition_success = 0;
    time lc_test_exit_timeout_ns = 120_000_000; // 120ms
    retval = uvm_hdl_check_path(LC_CTRL_TRANS_SUCCESS_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", LC_CTRL_TRANS_SUCCESS_PATH))
   `DV_SPINWAIT(while (transition_success == 0) begin
                  retval = uvm_hdl_read(LC_CTRL_TRANS_SUCCESS_PATH, transition_success);
                  `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", LC_CTRL_TRANS_SUCCESS_PATH))
                  cfg.clk_rst_vif.wait_clks(1);
                end,
                "timeout while wait for test exit complete",
                lc_test_exit_timeout_ns)
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Make sure entropy_src and csrng fuses are setup correctly independent
    // of which OTP image was loaded. The C portion of this test checks the
    // lc states across resets.
    cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg_partition(
      .device_id(DEVICE_ID), .manuf_state(MANUF_STATE),
      .en_sram_ifetch(MUBI8FALSE), .en_csrng_sw_app_read(MUBI8TRUE),
      .en_entropy_src_fw_read(MUBI8TRUE),
      .en_entropy_src_fw_over(MUBI8TRUE));
  endtask

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "LC transition in progress.",
             "wait for lc transition in progress",
             20_000_000);

    wait_for_transition();
    cfg.clk_rst_vif.wait_clks(1000);
    apply_reset();

  endtask
endclass : chip_sw_csrng_lc_hw_debug_en_vseq
