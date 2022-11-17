// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_all_escalation_resets_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_all_escalation_resets_vseq)

  `uvm_object_new

  // This associates a regex used to match the instance path and an alert number.
  typedef struct {
    string ip_inst_regex;
    byte alert_num;
  } ip_fatal_alert_t;

  ip_fatal_alert_t ip_alerts[] = '{
    '{"*adc_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdAdcCtrlAonFatalFault},
    '{"*aes*prim_reg_we_check*", TopEarlgreyAlertIdAesFatalFault},
    '{"*aon_timer*prim_reg_we_check*", TopEarlgreyAlertIdAonTimerAonFatalFault},
    '{"*clkmgr*prim_reg_we_check*", TopEarlgreyAlertIdClkmgrAonFatalFault},
    '{"*csrng*prim_reg_we_check*", TopEarlgreyAlertIdCsrngFatalAlert},
    '{"*edn0*prim_reg_we_check*", TopEarlgreyAlertIdEdn0FatalAlert},
    '{"*edn1*prim_reg_we_check*", TopEarlgreyAlertIdEdn1FatalAlert},
    '{"*entropy_src*prim_reg_we_check*", TopEarlgreyAlertIdEntropySrcFatalAlert},
    '{"*flash_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdFlashCtrlFatalStdErr},
    // TODO test u_eflash.u_flash alert TopEarlgreyAlertIdFlashCtrlFatalErr and
    // TODO TopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert.
    '{"*gpio*prim_reg_we_check*", TopEarlgreyAlertIdGpioFatalFault},
    '{"*hmac*prim_reg_we_check*", TopEarlgreyAlertIdHmacFatalFault},
    '{"*i2c0*prim_reg_we_check*", TopEarlgreyAlertIdI2c0FatalFault},
    '{"*i2c1*prim_reg_we_check*", TopEarlgreyAlertIdI2c1FatalFault},
    '{"*i2c2*prim_reg_we_check*", TopEarlgreyAlertIdI2c2FatalFault},
    '{"*keymgr*prim_reg_we_check*", TopEarlgreyAlertIdKeymgrFatalFaultErr},
    '{"*kmac*prim_reg_we_check*", TopEarlgreyAlertIdKmacFatalFaultErr},
    // TODO TopEarlgreyAlertIdLcCtrlFatalProgError: done in sw/device/tests/sim_dv/lc_ctrl_program_error.c?
    // TODO TopEarlgreyAlertIdLcCtrlFatalStateError. These don't have onehot_checkers, so they need an
    // alternative mechanism: maybe need to cause both u_reg, and u_reg_tap checkers?
    '{"*lc_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdLcCtrlFatalBusIntegError},
    '{"*otbn*prim_reg_we_check*", TopEarlgreyAlertIdOtbnFatal},
    // TODO TopEarlgreyAlertIdOtpCtrlFatalMacroError,
    // TODO TopEarlgreyAlertIdOtpCtrlFatalCheckError
    // TODO TopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert.
    '{"*otp_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdOtpCtrlFatalBusIntegError},
    '{"*pattgen*prim_reg_we_check*", TopEarlgreyAlertIdPattgenFatalFault},
    '{"*pinmux*prim_reg_we_check*", TopEarlgreyAlertIdPinmuxAonFatalFault},
    '{"*pwm*prim_reg_we_check*", TopEarlgreyAlertIdPwmAonFatalFault},
    '{"*pwrmgr*prim_reg_we_check*", TopEarlgreyAlertIdPwrmgrAonFatalFault},
    '{"*rom_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdRomCtrlFatal},
    '{"*rstmgr*prim_reg_we_check*", TopEarlgreyAlertIdRstmgrAonFatalFault},
    // TODO kTopEarlgreyAlertIdRstmgrAonFatalCnstyFault
    // TODO TopEarlgreyAlertIdRvCoreIbexFatalSwErr
    '{"*rv_core_ibex*prim_reg_we_check*", TopEarlgreyAlertIdRvCoreIbexFatalHwErr},
    '{"*rv_dm*prim_reg_we_check*", TopEarlgreyAlertIdRvDmFatalFault},
    // TODO kTopEarlgreyAlertIdRvPlicFatalFault
    '{"*rv_timer*prim_reg_we_check*", TopEarlgreyAlertIdRvTimerFatalFault},
    '{"*sensor_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdSensorCtrlFatalAlert},
    '{"*spi_device*prim_reg_we_check*", TopEarlgreyAlertIdSpiDeviceFatalFault},
    '{"*spi_host0*prim_reg_we_check*", TopEarlgreyAlertIdSpiHost0FatalFault},
    '{"*spi_host1*prim_reg_we_check*", TopEarlgreyAlertIdSpiHost1FatalFault},
    '{"*sram_ctrl_main*prim_reg_we_check*", TopEarlgreyAlertIdSramCtrlMainFatalError},
    '{"*sram_ctrl_ret*prim_reg_we_check*", TopEarlgreyAlertIdSramCtrlRetAonFatalError},
    '{"*sysrst_ctrl*prim_reg_we_check*", TopEarlgreyAlertIdSysrstCtrlAonFatalFault},
    '{"*uart0*prim_reg_we_check*", TopEarlgreyAlertIdUart0FatalFault},
    '{"*uart1*prim_reg_we_check*", TopEarlgreyAlertIdUart1FatalFault},
    '{"*uart2*prim_reg_we_check*", TopEarlgreyAlertIdUart2FatalFault},
    '{"*uart3*prim_reg_we_check*", TopEarlgreyAlertIdUart3FatalFault},
    '{"*usbdev*prim_reg_we_check*", TopEarlgreyAlertIdUsbdevFatalFault}
  };

  rand int ip_index;
  constraint ip_index_c {ip_index inside {[0 : ip_alerts.size() - 1]};}

  function int get_ip_index_from_name(string ip_name);
    string regex = {"*", ip_name, "*prim_reg_we_check*"};
    foreach (ip_alerts[i]) begin
      if (ip_alerts[i].ip_inst_regex == regex) return i;
    end
    `uvm_error(`gfn, $sformatf("%0s does not have a matched ip_index", ip_name))
  endfunction

  virtual task body();
    sec_cm_pkg::sec_cm_base_if_proxy if_proxy;
    ip_fatal_alert_t ip_alert;
    bit [7:0] sw_alert_num[];
    string actual_ip;
    if ($value$plusargs("inject_fatal_error_for_ip=%s", actual_ip)) begin
      ip_index = get_ip_index_from_name(actual_ip);
    end else begin
      string excluded_ips[$];
      int excluded_ip_idxs[$];
      `DV_GET_QUEUE_PLUSARG(excluded_ips, avoid_inject_fatal_error_for_ips)
      foreach (excluded_ips[i]) begin
        excluded_ip_idxs.push_back(get_ip_index_from_name(excluded_ips[i]));
      end
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(ip_index, !(ip_index inside {excluded_ip_idxs});)
    end

    ip_alert = ip_alerts[ip_index];

    // This sequence will trigger a fatal sec_cm failure.
    super.body();

    `uvm_info(`gfn, $sformatf(
              "Will inject fault for %s, expecting alert %0d",
              ip_alert.ip_inst_regex,
              ip_alert.alert_num
              ), UVM_MEDIUM)

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the expected alert.
    sw_alert_num = {ip_alert.alert_num};
    sw_symbol_backdoor_overwrite("kExpectedAlertNumber", sw_alert_num);

    ip_alert = ip_alerts[ip_index];
    if_proxy = sec_cm_pkg::find_sec_cm_if_proxy(.path(ip_alert.ip_inst_regex), .is_regex(1));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for fault injection",
             "Timeout waiting for fault injection request.")

    `uvm_info(`gfn, $sformatf(
              "Injecting fault for IP %s, with alert %0d",
              ip_alert.ip_inst_regex,
              ip_alert.alert_num
              ), UVM_MEDIUM);
    if_proxy.inject_fault();
  endtask
endclass
