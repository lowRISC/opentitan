// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_agent_cfg extends dv_base_agent_cfg;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual usb20_if vif;
  virtual usb20_block_if bif;
  virtual clk_rst_if clk_rst_if_i;

  `uvm_object_utils_begin(usb20_agent_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  bit usb_bitstuff_error = 1'b0; // This flag will be utilized in error scenarios to verify
  // the functionality of bit stuffing errors in the device. Set this flag in error cases,
  // check in the driver if it's set, then generate a bit stuffing error.

  bit single_bit_SE0 =1'b0; // This flag serves to evaluate the device's functionality,
  // particularly regarding the recognition of a single SE0 bit as an end-of-packet,
  // which necessitates two successive bits otherwise. Once set, it is accompanied by
  // its respective test sequence, followed by the transmission of a single-bit SE0 as EOP.

endclass
