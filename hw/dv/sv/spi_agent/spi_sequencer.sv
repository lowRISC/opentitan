// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_sequencer extends uvm_sequencer #(spi_item);
  `uvm_component_utils(spi_sequencer)

  spi_agent_cfg cfg;

  `uvm_component_new

endclass
