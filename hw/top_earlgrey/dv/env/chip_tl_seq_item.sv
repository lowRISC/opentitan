// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink sequence item override for the chip
// ---------------------------------------------
class chip_tl_seq_item extends tl_seq_item;

  // TODO: need to capture this as param
  constraint a_source_c {
    a_source inside {[0:1]};
  }

  `uvm_object_utils_begin(chip_tl_seq_item)
  `uvm_object_utils_end

  `uvm_object_new

endclass
