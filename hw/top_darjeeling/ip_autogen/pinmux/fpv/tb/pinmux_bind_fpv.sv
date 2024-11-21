// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module pinmux_bind_fpv;


  bind pinmux pinmux_assert_fpv #(
    .TargetCfg(TargetCfg),
    .AlertAsyncOn(AlertAsyncOn),
    .SecVolatileRawUnlockEn(SecVolatileRawUnlockEn)
  ) i_pinmux_assert_fpv (
    .clk_i,
    .rst_ni,
    .rst_sys_ni,
    .scanmode_i,
    .clk_aon_i,
    .rst_aon_ni,
    .pin_wkup_req_o,
    .sleep_en_i,
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
