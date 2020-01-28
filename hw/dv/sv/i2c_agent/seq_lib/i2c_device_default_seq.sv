// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// drive everything 0 for testing break error
class i2c_device_default_seq extends i2c_device_seq;
  `uvm_object_utils(i2c_device_default_seq)

  // limit constraints to a deterministic configuration for debug
  constraint addr_c      { addr             == 51; }   // addr[0]=R/W=1'b1: read
  constraint wr_data_c   { wr_data          == 15; }
  constraint rd_data_c   { rd_data          == 25; }
  constraint mem_datas_c { mem_datas.size() == 64; }
  constraint mem_addrs_c { mem_addrs.size() == 64; }

  `uvm_object_new

endclass : i2c_device_default_seq
