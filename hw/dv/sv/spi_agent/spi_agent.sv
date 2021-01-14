// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_agent extends dv_base_agent#(
    .CFG_T          (spi_agent_cfg),
    .DRIVER_T       (spi_driver),
    .HOST_DRIVER_T  (spi_host_driver),
    .DEVICE_DRIVER_T(spi_device_driver),
    .SEQUENCER_T    (spi_sequencer),
    .MONITOR_T      (spi_monitor),
    .COV_T          (spi_agent_cov)
  );
  `uvm_component_utils(spi_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // get spi_if handle
    if (!uvm_config_db#(virtual spi_if)::get(this, "", "vif", cfg.vif))
      `uvm_fatal(`gfn, "failed to get spi_if handle from uvm_config_db")
  endfunction

endclass
