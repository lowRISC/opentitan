// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(spi_host_env_cfg),
    .COV_T(spi_host_env_cov)
  );

  spi_sequencer  spi_sequencer_h;

  `uvm_component_utils(spi_host_virtual_sequencer)
  `uvm_component_new

endclass : spi_host_virtual_sequencer
