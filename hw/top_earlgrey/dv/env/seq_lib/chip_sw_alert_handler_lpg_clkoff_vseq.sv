// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_lpg_clkoff_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_alert_handler_lpg_clkoff_vseq)

  `uvm_object_new

  // The list of IPs tested in this test. This enumeration must match the array in
  // sw/device/tests/alert_handler_lpg_clkoff_test.c::kPeripherals[].
  typedef enum {
    Aes,
    Hmac,
    Kmac,
    Otbn,
    SpiHost0,
    SpiHost1,
    Usbdev,
    IpCount
  } ips_tested_e;

  typedef struct {
    string if_proxy_regex;
    sec_cm_pkg::sec_cm_base_if_proxy if_proxy;
    int unsigned fatal_alert_id;
  } ip_fatal_alert_t;

  ip_fatal_alert_t ip_fatal_alerts[] = '{
    '{"*aes*prim_reg_we_check*", null, TopEarlgreyAlertIdAesFatalFault},
    '{"*hmac*prim_reg_we_check*", null, TopEarlgreyAlertIdHmacFatalFault},
    '{"*kmac*prim_reg_we_check*", null, TopEarlgreyAlertIdKmacFatalFaultErr},
    '{"*otbn*prim_reg_we_check*", null, TopEarlgreyAlertIdOtbnFatal},
    '{"*spi_host0*prim_reg_we_check*", null, TopEarlgreyAlertIdSpiHost0FatalFault},
    '{"*spi_host1*prim_reg_we_check*", null, TopEarlgreyAlertIdSpiHost1FatalFault},
    '{"*usbdev*prim_reg_we_check*", null, TopEarlgreyAlertIdUsbdevFatalFault}
  };

  virtual task pre_start();
    // The wait-time between two ping requests is a 16-bit value, coming from an LFSR.
    // In DV, we force the wait-time to known fixed value so that the alert handler's ping mechanism
    // is able to hit all blocks within a reasonable amount of simulated / wall clock time. We pick
    // 7 which is the minimum-allowed value.
    void'(cfg.chip_vif.signal_probe_alert_handler_ping_timer_wait_cyc_mask_i(SignalProbeForce, 7));
    super.pre_start();
  endtask

  virtual task body();
    string anchor = "Peripheral %0d ready for fault injection";

    super.body();

    // Construct the ip_fatal_alerts data structure.
    for (int i = 0; i < IpCount; i++) begin
      ip_fatal_alerts[i].if_proxy = sec_cm_pkg::find_sec_cm_if_proxy(
          .path(ip_fatal_alerts[i].if_proxy_regex), .is_regex(1));
    end

    // In test phase 2, we inject a fault in peripherals whose clocks are turned off, to ensure that
    // the fatal alert continues to fire after the clock is turned back on.
    // Loop through the IPs, injecting a fault as expected by the SW test.
    for (int i = 0; i < IpCount; i++) begin
      ips_tested_e ip = ips_tested_e'(i);
      `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == $sformatf(anchor, i))
      cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(200, 500));
      `uvm_info(`gfn, $sformatf("Injecting a fatal alert in %0s", ip.name()), UVM_LOW)
      ip_fatal_alerts[i].if_proxy.inject_fault();
      // Verify that the alert triggered (the SW does the same via frontdoor CSR read).
      // By virtue of automation, the cfg.list_of_alerts string names follow the same enumeration as
      // the alert indices in top_earlgrey_pkg::alert_id_e.
      wait_alert_trigger(cfg.list_of_alerts[ip_fatal_alerts[i].fatal_alert_id], .max_wait_cycle(2));
      // The SW turns the clock to the peripheral off and then back on. Wait for those events.
      wait_clk_status(ip, 0);
      wait_clk_status(ip, 1);
    end
  endtask

  // Waits for the clock to the chosen IP to be enabled or gated.
  task wait_clk_status(ips_tested_e ip, bit is_enabled);
    case(ip)
      Aes:      `DV_WAIT(cfg.chip_vif.aes_clk_is_enabled == is_enabled)
      Hmac:     `DV_WAIT(cfg.chip_vif.hmac_clk_is_enabled == is_enabled)
      Kmac:     `DV_WAIT(cfg.chip_vif.kmac_clk_is_enabled == is_enabled)
      Otbn:     `DV_WAIT(cfg.chip_vif.otbn_clk_is_enabled == is_enabled)
      SpiHost0: `DV_WAIT(cfg.chip_vif.io_clk_is_enabled == is_enabled)
      SpiHost1: `DV_WAIT(cfg.chip_vif.io_div2_clk_is_enabled == is_enabled)
      Usbdev:   `DV_WAIT(cfg.chip_vif.usbdev_clk_is_enabled == is_enabled)
      default:  `uvm_fatal(`gfn, $sformatf("Invalid IP: %0d", ip))
    endcase
  endtask

  virtual task post_start();
    // Wait for the SW test to finsh.
    super.post_start();

    // Restore the DUT back to a clean state.
    apply_reset();
  endtask

endclass
