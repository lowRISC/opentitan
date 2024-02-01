// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ${module_instance_name}_bind_fpv;

  import ${module_instance_name}_reg_pkg::*;

  bind ${module_instance_name} ${module_instance_name}_assert_fpv #(
    .NumSrc(${module_instance_name}_reg_pkg::NumSrc),
    .NumTarget(${module_instance_name}_reg_pkg::NumTarget),
    .NumAlerts(${module_instance_name}_reg_pkg::NumAlerts),
    .PRIOW(${module_instance_name}_reg_pkg::PrioWidth)
  ) ${module_instance_name}_assert_fpv(
    .clk_i,
    .rst_ni,
    .intr_src_i,
    .alert_rx_i,
    .alert_tx_o,
    .irq_o,
    .irq_id_o,
    .msip_o,
    .ip,
    .ie,
    .claim,
    .complete,
    .prio,
    .threshold
  );

  bind ${module_instance_name} tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind ${module_instance_name} ${module_instance_name}_csr_assert_fpv ${module_instance_name}_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

endmodule : ${module_instance_name}_bind_fpv
