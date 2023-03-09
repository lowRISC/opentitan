// Copyright lowRISC contributors.
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
    bit [TL_AW-1:0] hw_cfg_addr = otp_ctrl_reg_pkg::HwCfgOffset;
    bit [TL_DW-1:0] val;
    bit [7:0] sw_alert_num[];

    super.body();

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the expected alert.
    sw_alert_num = {TopEarlgreyAlertIdOtpCtrlFatalMacroError};
    sw_symbol_backdoor_overwrite("kExpectedAlertNumber", sw_alert_num);

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for fault injection",
             "Timeout waiting for fault injection request.")

    val = cfg.mem_bkdr_util_h[Otp].read32(hw_cfg_addr);

    // Inject 2 bits error in this hw_cfg_addr to trigger a ECC non-correctable error.
    cfg.mem_bkdr_util_h[Otp].inject_errors(hw_cfg_addr, 2);


    `DV_WAIT(cfg.sw_logger_vif.printed_log == "OTP_CTRL error inject done",
             "Timeout waiting for OTP_CTRL error injection done.")

    // TODO: backdoor check if alerts are firing.

    // Backdoor write back the original value so the chip can reboot successfully.
    cfg.mem_bkdr_util_h[Otp].write32(hw_cfg_addr, val);

  endtask

endclass
