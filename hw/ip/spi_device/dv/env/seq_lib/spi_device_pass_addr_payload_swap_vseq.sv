// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test passthrough mode address/payload translation scenario, addr/payload_swap_en on and off
class spi_device_pass_addr_payload_swap_vseq extends spi_device_pass_cmd_filtering_vseq;
  `uvm_object_utils(spi_device_pass_addr_payload_swap_vseq)
  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    allow_addr_swap = 1;
    allow_payload_swap = 1;
    addr_payload_swap_pct = 100;
  endtask : pre_start

endclass : spi_device_pass_addr_payload_swap_vseq
