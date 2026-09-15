// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This virtual sequence triggers OTP macro and check fatal errors by backdoor injecting ECC errors
// and read back the injected error via DAI interface.
// Because these fatal alert in OTP immediately will send the error information to LC_CTRL and turn
// off CPU, this sequence will check alerts via backdoor probing.

class chip_sw_otp_ctrl_escalation_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_otp_ctrl_escalation_vseq)

  `uvm_object_new

  virtual task body();
    bit [TL_AW-1:0] hw_cfg_addr = otp_ctrl_reg_pkg::HwCfg0Offset;
    row_data_t      val;
    bit [7:0] sw_alert_num[];

    super.body();

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the expected alert.
    sw_alert_num = {TopEarlgreyAlertIdOtpCtrlFatalMacroError};
    sw_symbol_backdoor_overwrite("kExpectedAlertNumber", sw_alert_num);

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for fault injection",
             "Timeout waiting for fault injection request.")

    // inject_errors() may flip any bit of the row, so save the whole row.
    val = cfg.mem_bkdr_util_h[Otp].read(hw_cfg_addr);

    // Inject 2 bits error in this hw_cfg_addr to trigger a ECC non-correctable error.
    // The CPU runs from RRAM, so wait until no row read is awaiting its verification read.
    wait_rram_rd_buf_rdy();
    cfg.mem_bkdr_util_h[Otp].inject_errors(hw_cfg_addr, 2);


    `DV_WAIT(cfg.sw_logger_vif.printed_log == "OTP_CTRL error inject done",
             "Timeout waiting for OTP_CTRL error injection done.")
    // SW logs that after starting the DAI read, not after it completes.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusUnderReset,
             "Timeout waiting for the escalation reset to start.")

    // TODO: backdoor check if alerts are firing.

    // Backdoor write back the original value so the chip can reboot successfully.
    cfg.mem_bkdr_util_h[Otp].write(hw_cfg_addr, val);

  endtask

endclass
