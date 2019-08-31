// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_virtual_sequencer extends cip_base_virtual_sequencer #(
      .CFG_T(spi_device_env_cfg),
      .COV_T(spi_device_env_cov)
    );
  `uvm_component_utils(spi_device_virtual_sequencer)

  spi_sequencer  spi_sequencer_h;

  `uvm_component_new

endclass
