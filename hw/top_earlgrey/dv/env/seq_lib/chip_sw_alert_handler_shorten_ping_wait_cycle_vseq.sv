// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_alert_handler_shorten_ping_wait_cycle_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_alert_handler_shorten_ping_wait_cycle_vseq)

  `uvm_object_new

  virtual task pre_start();
    // The wait-time between two ping requests is a 16-bit value, coming from an LFSR.
    // In DV, the wait-time can be overridden by using ping_timer's wait_cyc_mask_i input,
    // which is a right-aligned mask. For more info:
    // https://github.com/lowRISC/opentitan/blob/master/hw/ip_templates/alert_handler/rtl/alert_handler.sv#L132-L136
    //
    // The minimum-allowed value,7, is chosen here to use only the least-significant 3 bits of
    // the LFSR output as the wait-time between two ping requests.
    void'(cfg.chip_vif.signal_probe_alert_handler_ping_timer_wait_cyc_mask_i(SignalProbeForce, 7));
    super.pre_start();
  endtask

  string signal_forced;
  virtual task body();

    super.body();

///*
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert AES")
    signal_forced = "tb.dut.top_earlgrey.u_aes.gen_alert_tx[1].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert HMAC")
    signal_forced = "tb.dut.top_earlgrey.u_hmac.gen_alert_tx[0].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert KMAC")
    signal_forced = "tb.dut.top_earlgrey.u_kmac.gen_alert_tx[1].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert OTBN")
    signal_forced = "tb.dut.top_earlgrey.u_otbn.gen_alert_tx[0].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

   `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert SPI_HOST0")
    signal_forced = "tb.dut.top_earlgrey.u_spi_host0.gen_alert_tx[0].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert SPI_HOST1")
    signal_forced = "tb.dut.top_earlgrey.u_spi_host1.gen_alert_tx[0].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Trigger fatal alert USB")
    signal_forced = "tb.dut.top_earlgrey.u_usbdev.gen_alert_tx[0].u_prim_alert_sender.alert_req_i";
    `DV_CHECK(uvm_hdl_force(signal_forced, 1'b1))
    #200ns;
    `DV_CHECK(uvm_hdl_release(signal_forced))

  endtask

  //task post_start();
   // expect_fatal_alerts = 1;
  //  super.post_start();
 // endtask

endclass
