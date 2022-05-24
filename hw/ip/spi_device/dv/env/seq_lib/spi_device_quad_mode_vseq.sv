// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Output command in quad mode test
class spi_device_quad_mode_vseq extends spi_device_dual_mode_vseq;
  `uvm_object_utils(spi_device_quad_mode_vseq)
  `uvm_object_new

  constraint op_cmd_c {
    op_cmd == READ_QUAD;
  };
  constraint num_lanes_c {
    num_lanes == 3'h4;
  };

endclass : spi_device_quad_mode_vseq
