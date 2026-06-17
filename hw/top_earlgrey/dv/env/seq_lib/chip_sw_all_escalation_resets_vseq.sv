// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_all_escalation_resets_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_all_escalation_resets_vseq)

  typedef struct {
    // A shell glob that represents the instance path. This is matched with a * at each end (so
    // "bar" will match "foobarqux")
    string ip_inst_glob;

    // The countermeasure by which we will trigger an alert. If this is the empty string, it
    // defaults to default_cm_name (to avoid having to write a string lots of times in the file)
    string countermeasure;

    // The index of the alert that the countermeasure will generate
    int unsigned alert_num;
  } ip_fatal_alert_t;

  // The default countermeasure name for an ip_fatal_alert_t: if its countermeasure field is empty,
  // this is the countermeasure selected.
  string default_cm_name = "prim_reg_we_check";

  ip_fatal_alert_t ip_alerts[] = '{
    '{"adc_ctrl", "", TopEarlgreyAlertIdAdcCtrlAonFatalFault},
    '{"aes", "", TopEarlgreyAlertIdAesFatalFault},
    '{"aon_timer", "", TopEarlgreyAlertIdAonTimerAonFatalFault},
    '{"clkmgr", "", TopEarlgreyAlertIdClkmgrAonFatalFault},
    '{"csrng", "", TopEarlgreyAlertIdCsrngFatalAlert},
    '{"edn0", "", TopEarlgreyAlertIdEdn0FatalAlert},
    '{"edn1", "", TopEarlgreyAlertIdEdn1FatalAlert},
    '{"entropy_src", "", TopEarlgreyAlertIdEntropySrcFatalAlert},
    '{"flash_ctrl", "", TopEarlgreyAlertIdFlashCtrlFatalStdErr},
    // test u_eflash.u_flash alert TopEarlgreyAlertIdFlashCtrlFatalErr is implemented in the
    // `chip_sw_flash_host_gnt_err_inj_vseq` sequence.
    '{"flash_ctrl*.u_flash", "", TopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert},
    '{"gpio", "", TopEarlgreyAlertIdGpioFatalFault},
    '{"hmac", "", TopEarlgreyAlertIdHmacFatalFault},
    '{"i2c0", "", TopEarlgreyAlertIdI2c0FatalFault},
    '{"i2c1", "", TopEarlgreyAlertIdI2c1FatalFault},
    '{"i2c2", "", TopEarlgreyAlertIdI2c2FatalFault},
    '{"keymgr", "", TopEarlgreyAlertIdKeymgrFatalFaultErr},
    '{"kmac", "", TopEarlgreyAlertIdKmacFatalFaultErr},
    // TODO TopEarlgreyAlertIdLcCtrlFatalProgError: done in .../sim_dv/lc_ctrl_program_error.c?
    '{"lc_ctrl", "state_regs", TopEarlgreyAlertIdLcCtrlFatalStateError},
    '{"lc_ctrl", "", TopEarlgreyAlertIdLcCtrlFatalBusIntegError},
    '{"otbn", "", TopEarlgreyAlertIdOtbnFatal},
    // TopEarlgreyAlertIdOtpCtrlFatalMacroError: done in chip_sw_otp_ctrl_escalation_vseq
    '{"otp_ctrl", "u_otp_ctrl_dai", TopEarlgreyAlertIdOtpCtrlFatalCheckError},
    '{"otp_ctrl", "", TopEarlgreyAlertIdOtpCtrlFatalBusIntegError},
    '{"pattgen", "", TopEarlgreyAlertIdPattgenFatalFault},
    '{"pinmux", "", TopEarlgreyAlertIdPinmuxAonFatalFault},
    '{"pwm", "", TopEarlgreyAlertIdPwmAonFatalFault},
    '{"pwrmgr", "", TopEarlgreyAlertIdPwrmgrAonFatalFault},
    '{"rom_ctrl", "", TopEarlgreyAlertIdRomCtrlFatal},
    '{"rstmgr", "", TopEarlgreyAlertIdRstmgrAonFatalFault},
    // TopEarlgreyAlertIdRstmgrAonFatalCnstyFault cannot use this test.
    //
    '{"rv_core_ibex", "sw_fatal_err", TopEarlgreyAlertIdRvCoreIbexFatalSwErr},
    '{"rv_core_ibex", "", TopEarlgreyAlertIdRvCoreIbexFatalHwErr},
    '{"rv_dm", "", TopEarlgreyAlertIdRvDmFatalFault},
    '{"rv_plic", "", TopEarlgreyAlertIdRvPlicFatalFault},
    '{"rv_timer", "", TopEarlgreyAlertIdRvTimerFatalFault},
    '{"sensor_ctrl", "", TopEarlgreyAlertIdSensorCtrlAonFatalAlert},
    '{"spi_device", "", TopEarlgreyAlertIdSpiDeviceFatalFault},
    '{"spi_host0", "", TopEarlgreyAlertIdSpiHost0FatalFault},
    '{"spi_host1", "", TopEarlgreyAlertIdSpiHost1FatalFault},
    '{"sram_ctrl_main", "", TopEarlgreyAlertIdSramCtrlMainFatalError},
    '{"sram_ctrl_ret", "", TopEarlgreyAlertIdSramCtrlRetAonFatalError},
    '{"sysrst_ctrl", "", TopEarlgreyAlertIdSysrstCtrlAonFatalFault},
    '{"uart0", "", TopEarlgreyAlertIdUart0FatalFault},
    '{"uart1", "", TopEarlgreyAlertIdUart1FatalFault},
    '{"uart2", "", TopEarlgreyAlertIdUart2FatalFault},
    '{"uart3", "", TopEarlgreyAlertIdUart3FatalFault},
    '{"usbdev", "", TopEarlgreyAlertIdUsbdevFatalFault}
  };

  function new (string name="");
    super.new(name);
  endfunction

  // Return the index of an entry in ip_alerts for the requested ip and security counter-measure,
  // searching by name.
  //
  // Fail with an error if there is no matching entry.
  function int unsigned get_ip_index_from_name(string ip_name, string sec_cm);
    bit allow_empty = (sec_cm == default_cm_name);

    foreach (ip_alerts[i]) begin
      if (ip_alerts[i].ip_inst_glob == ip_name &&
          (ip_alerts[i].countermeasure == sec_cm ||
           (allow_empty && ip_alerts[i].countermeasure == ""))) begin
        return i;
      end
    end
    `uvm_error(get_full_name(), $sformatf("Unknown ip/sec_cm pair: %0s/%0s.", ip_name, sec_cm))
    return 0;
  endfunction

  // Split str into an ip_name shell glob and countermeasure, splitting on the last '*'. If there is
  // no '*' in the string, treat the whole thing as an ip_name shell glob and output
  // default_cm_name for sec_cm.
  function void tokenize_ip_and_countermeasure(string        str,
                                               output string ip_name,
                                               output string sec_cm);
    bit          found_star;
    int unsigned last_star_idx;

    for (int unsigned i = 0; i < str.len(); i++) begin
      if (str.getc(i) == "*") begin
        last_star_idx = i;
        found_star = 1;
      end
    end

    if (found_star) begin
      ip_name = str.substr(0, last_star_idx - 1);
      sec_cm = str.substr(last_star_idx + 1, str.len() - 1);
    end else begin
      ip_name = str;
      sec_cm = default_cm_name;
    end
  endfunction

  // Consume the plusarg called plusarg_name, whose value should be a comma-separated list of
  // strings. Append each of those strings to queue.
  function void append_queue_plusarg(string plusarg_name, ref string queue[$]);
    string plusarg_val;
    if ($value$plusargs({plusarg_name, "=%0s"}, plusarg_val)) begin
      string words[$];
      str_split(plusarg_val, words, ",");
      foreach (words[i]) begin
        queue.push_back(words[i]);
      end
    end
  endfunction

  // Look at the entries in the +avoid_inject_fatal_error_for_ips plusarg and add the associated
  // indices in ip_alerts to excluded_indices.
  function void get_excluded_indices(ref int unsigned excluded_indices[$]);
    string excluded_ips[$];
    append_queue_plusarg("avoid_inject_fatal_error_for_ips", excluded_ips);

    foreach (excluded_ips[i]) begin
      string ip_name, sec_cm;
      tokenize_ip_and_countermeasure(excluded_ips[i], ip_name, sec_cm);
      excluded_indices.push_back(get_ip_index_from_name(ip_name, sec_cm));
    end
  endfunction

  // Return the countermeasure field for an ip_fatal_alert_t (expanding "" to default_cm_name)
  function string cm_for_alert(const ref ip_fatal_alert_t alert);
    return (alert.countermeasure == "") ? default_cm_name : alert.countermeasure;
  endfunction

  // Return a shell glob for the sec_cm_base_if_proxy for the requested item
  function string glob_for_alert(const ref ip_fatal_alert_t alert);
    return {"*", alert.ip_inst_glob, "*", cm_for_alert(alert), "*"};
  endfunction

  // Search the registered sec_cm proxies and return one that matches the requested item
  //
  // If non match, fail with an error.
  function sec_cm_pkg::sec_cm_base_if_proxy find_proxy_for_alert(const ref ip_fatal_alert_t alert);
    return sec_cm_pkg::find_sec_cm_if_proxy(.path(glob_for_alert(alert)), .is_regex(1));
  endfunction

  virtual task body();
    int unsigned         ip_idx;
    int unsigned         excluded_ip_idxs[$];
    ip_fatal_alert_t     ip_alert;
    bit [7:0]            sw_alert_num[];

    get_excluded_indices(excluded_ip_idxs);

    if (!std::randomize(ip_idx) with {
          ip_idx < ip_alerts.size();
          !(ip_idx inside {excluded_ip_idxs});
        }) begin
      `uvm_fatal(get_full_name(), "Failed to randomize ip_idx")
    end
    ip_alert = ip_alerts[ip_idx];

    // Run chip_sw_base_vseq::body, which will start the SW on the CPU
    super.body();

    `uvm_info(get_full_name(),
              $sformatf("Will trigger countermeasure %0s in IP block at %0s, expecting alert %0d",
                        cm_for_alert(ip_alert), ip_alert.ip_inst_glob, ip_alert.alert_num),
              UVM_LOW)

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the expected alert.
    sw_alert_num = {ip_alert.alert_num};
    sw_symbol_backdoor_overwrite("kExpectedAlertNumber", sw_alert_num);

    if (ip_alert.alert_num == TopEarlgreyAlertIdRvCoreIbexFatalSwErr) begin
      `uvm_info(`gfn, "Testing Software fatal alert, no fault to inject", UVM_MEDIUM)
      return;
    end

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for fault injection",
             "Timeout waiting for fault injection request.")

    `uvm_info(get_full_name(),
              $sformatf("Injecting fault for IP block at %0s, with alert %0d",
                        ip_alert.ip_inst_glob, ip_alert.alert_num),
              UVM_LOW);
    find_proxy_for_alert(ip_alert).inject_fault();
  endtask
endclass
