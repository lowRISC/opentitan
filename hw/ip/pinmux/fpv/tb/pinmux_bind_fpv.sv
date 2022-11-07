// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module pinmux_bind_fpv;


  bind pinmux pinmux_assert_fpv #(
    .TargetCfg(TargetCfg),
    .AlertAsyncOn(AlertAsyncOn)
  ) i_pinmux_assert_fpv (
    .clk_i,
    .rst_ni,
    .rst_sys_ni,
    .scanmode_i,
    .clk_aon_i,
    .rst_aon_ni,
    .pin_wkup_req_o,
    .usb_wkup_req_o,
    .sleep_en_i,
    .strap_en_i,
    .lc_dft_en_i,
    .lc_hw_debug_en_i,
    .lc_check_byp_en_i,
    .lc_escalate_en_i,
    .pinmux_hw_debug_en_o,
    .dft_strap_test_o,
    .dft_hold_tap_sel_i,
    .lc_jtag_o,
    .lc_jtag_i,
    .rv_jtag_o,
    .rv_jtag_i,
    .dft_jtag_o,
    .dft_jtag_i,
    .usbdev_dppullup_en_i,
    .usbdev_dnpullup_en_i,
    .usb_dppullup_en_o,
    .usb_dnpullup_en_o,
    .usbdev_suspend_req_i,
    .usbdev_wake_ack_i,
    .usbdev_bus_reset_o,
    .usbdev_sense_lost_o,
    .usbdev_wake_detect_active_o,
    .tl_i,
    .tl_o,
    .alert_rx_i,
    .alert_tx_o,
    .periph_to_mio_i,
    .periph_to_mio_oe_i,
    .mio_to_periph_o,
    .periph_to_dio_i,
    .periph_to_dio_oe_i,
    .dio_to_periph_o,
    .mio_attr_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i,
    .dio_attr_o,
    .dio_out_o,
    .dio_oe_o,
    .dio_in_i
  );


  bind pinmux tlul_assert #(
    .EndpointType("Device")
  ) i_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o),
    .*
  );

  bind pinmux pinmux_csr_assert_fpv i_pinmux_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

endmodule : pinmux_bind_fpv
