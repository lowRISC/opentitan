// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Memory walk for the windows of the I3C block.
//
// The generic walk covers the memories that are not excluded from it (see
// `i3c_env_cfg::set_mem_walk_excls()`). The Device Address Table (DAT) and the Device
// Characteristics Table (DCT) store their entries without the reserved fields of the HCI
// specification, which read as zero. The generic walk cannot compare such words, so this sequence
// walks those two tables with a per-word mask of the stored bits.
class i3c_csr_mem_walk_seq extends csr_mem_walk_seq;
  `uvm_object_utils(i3c_csr_mem_walk_seq)

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t dat_masks[$], dct_masks[$];
    get_dat_word_masks(dat_masks);
    get_dct_word_masks(dct_masks);

    super.body();
    foreach (models[i]) begin
      i3c_reg_block ral;
      `downcast(ral, models[i])
      masked_walk(ral.dat, dat_masks);
      masked_walk(ral.dct, dct_masks);
    end
  endtask : body

  // Walk through `mem` like `uvm_mem_walk_seq`, comparing only the bits in the mask of each word.
  // The masks repeat every `masks.size()` words.
  protected virtual task masked_walk(uvm_mem mem, uvm_reg_data_t masks[$]);
    uvm_reg_map    map  = mem.get_default_map();
    longint        size = mem.get_size();
    uvm_status_e   status;
    uvm_reg_data_t val;

    `uvm_info(`gfn, $sformatf("Walking memory %0s with masks", mem.get_full_name()), UVM_LOW)
    `DV_CHECK_FATAL(masks.size() > 0)
    `DV_CHECK_EQ_FATAL(size % masks.size(), 0)

    // Write the inverted address to every word.
    for (longint k = 0; k < size; k++) begin
      mem.write(status, k, ~k, UVM_FRONTDOOR, map, this);
      `DV_CHECK_EQ(status, UVM_IS_OK, $sformatf("Write to %0s[%0d]", mem.get_name(), k))
    end

    // Check each word, then overwrite it with its address and check that this does not affect the
    // preceding word.
    for (longint k = 0; k < size; k++) begin
      uvm_reg_data_t mask = masks[k % masks.size()];
      mem.read(status, k, val, UVM_FRONTDOOR, map, this);
      `DV_CHECK_EQ(status, UVM_IS_OK, $sformatf("Read from %0s[%0d]", mem.get_name(), k))
      `DV_CHECK_EQ(val, ~k & mask, $sformatf("%0s[%0d]", mem.get_name(), k))

      mem.write(status, k, k, UVM_FRONTDOOR, map, this);
      `DV_CHECK_EQ(status, UVM_IS_OK, $sformatf("Write to %0s[%0d]", mem.get_name(), k))
      if (k > 0) begin
        mask = masks[(k - 1) % masks.size()];
        mem.read(status, k - 1, val, UVM_FRONTDOOR, map, this);
        `DV_CHECK_EQ(status, UVM_IS_OK, $sformatf("Read from %0s[%0d]", mem.get_name(), k - 1))
        `DV_CHECK_EQ(val, (k - 1) & mask, $sformatf("%0s[%0d]", mem.get_name(), k - 1))
      end
    end

    // Check the final word, which the loop above writes but does not read back.
    mem.read(status, size - 1, val, UVM_FRONTDOOR, map, this);
    `DV_CHECK_EQ(status, UVM_IS_OK, $sformatf("Read from %0s[%0d]", mem.get_name(), size - 1))
    `DV_CHECK_EQ(val, (size - 1) & masks[(size - 1) % masks.size()],
                 $sformatf("%0s[%0d]", mem.get_name(), size - 1))
  endtask : masked_walk

endclass : i3c_csr_mem_walk_seq
