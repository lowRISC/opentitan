// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual usb20_block_if bif;
  virtual clk_rst_if clk_rst_if_i;

  `uvm_object_utils_begin(usb20_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // If this is set then the driver will generate a bit stuffing error.
  bit usb_bitstuff_error = 1'b0;
  // This flag serves to evaluate the device's functionality,
  // particularly regarding the recognition of a single SE0 bit as an end-of-packet,
  // which necessitates two successive bits otherwise. Once set, it is accompanied by
  // its respective test sequence, followed by the transmission of a single-bit SE0 as EOP.
  bit single_bit_SE0 = 1'b0;
  // used as a time_out signal when device timeouts.
  bit time_out = 1'b0;
endclass
