// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test performs a the first two steps of a ROM bootstrap operation, i.e., flash erase followed
// by a single page program operation. It then confirms flash has been programmed, by backdoor
// reading back the first data page.

class chip_sw_ate_bootstrap_disjoint_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ate_bootstrap_disjoint_vseq)

  function new(string name="");
    super.new(name);
  endfunction

  virtual task body();
    int unsigned num_errors = 0;
    string       sw_image;
    byte         sw_byte_q[$];

    // The base class body function calls cpu_init, which calls spi_device_load_bootstrap. This will
    // load up the contents of the firmware image into the two banks of flash. That will only happen
    // if a SW image exists: make sure it does and fail quickly if not.
    if (!cfg.sw_images.exists(SwTypeTestSlotA)) begin
      `uvm_fatal(get_name(), "Slot A image doesn't exist.")
    end

    super.body();

    // Read the SW frames again into a local queue. This feels a little silly (because we did it in
    // the base class as well), but it's reasonably quick.
    sw_image = {cfg.sw_images[SwTypeTestSlotA], ".64.vmem"};
    read_sw_frames(sw_image, sw_byte_q);

    // Read back the programmed flash data page to confirm it was programmed correctly.
    for (int a = 0; a < sw_byte_q.size; a += 4) begin
      bit [31:0] expected = {sw_byte_q[a + 3], sw_byte_q[a + 2],
                             sw_byte_q[a + 1], sw_byte_q[a + 0]};
      if (!check_flash_word_32(a, expected)) num_errors++;
    end
    if (num_errors > 0) begin
      `uvm_error(get_name(),
                 $sformatf("Found %0d errors when checking programmed flash", num_errors))
    end

    // Set test passed.
    assert_por_reset();
    override_test_status_and_finish(.passed(1'b1));
  endtask

  // This overrides a task in chip_sw_base_vseq
  //
  // We run the normal version *unless* the relevant range of byte_q happens to only contain 'hff.
  // If it does, there is no need to write the page: we know that we have just erased flash to that
  // value anyway.
  protected virtual task spi_write_flash_page(const ref byte byte_q[$],
                                              int unsigned start_idx,
                                              int unsigned page_size);
    bit found_low_bit = 0;
    for (int unsigned i = start_idx; i - start_idx < page_size && i < byte_q.size(); i++) begin
      if (byte_q[i] != 8'hff) begin
        found_low_bit = 1;
        break;
      end
    end

    if (found_low_bit) begin
      `uvm_info(get_name(), $sformatf("Sending page from offset 0x%0h", start_idx), UVM_LOW)
      super.spi_write_flash_page(byte_q, start_idx, page_size);
    end else begin
      `uvm_info(get_name(),
                $sformatf("Skipping page at offset 0x%0h (all the bits are set)", start_idx),
                UVM_LOW)
    end
  endtask

  // Do a backdoor read of a 32-bit word in flash. On a match, return true. On a mismatch, generate
  // a uvm_error describing the mismatch and return false.
  //
  local function bit check_flash_word_32(int unsigned address, bit [31:0] expected);
    int unsigned     rel_address;
    chip_mem_e       mem_idx;
    logic [31:0]     actual;

    if (!expand_flash_address(address, rel_address, mem_idx)) begin
      `uvm_error(get_name(), $sformatf("Cannot interpret 0x%0h as a flash address.", address))
      return 1'b0;
    end

    // At this point, we know the slot and offset for the address. Look up the associated backdoor
    // and check that there is actually flash memory backing the address.
    if (rel_address >= cfg.mem_bkdr_util_h[mem_idx].get_depth()) begin
      `uvm_error(get_name(),
                 $sformatf({"Address 0x%0h is interpreted as offset 0x%0h with mem_idx %0d, but ",
                            "that bank only has a depth of 0x%0h."},
                           address, rel_address, mem_idx, cfg.mem_bkdr_util_h[mem_idx].get_depth()))
      return 1'b0;
    end

    actual = cfg.mem_bkdr_util_h[mem_idx].read32(rel_address);

    if (actual === expected) begin
      return 1'b1;
    end else begin
      `uvm_error(get_name(),
                 $sformatf({"Flash data mismatch at 0x%0h (mem_idx %0p; rel_address 0x%0h). ",
                            "We expected 0x%0h but saw 0x%0h."},
                           address, mem_idx, rel_address, expected, actual))
      return 1'b0;
    end
  endfunction

  // Extract a SW flash address into a bank index and address within the bank
  //
  // The address is from the SW point of view, which is actually governed by the rom_ext slot
  // addresses in ../../../defs.bzl. That mapping is replicated here, and we expect:
  //
  //    - Slot A addresses 0x00000 - 0x7ffff
  //    - Slot B addresses 0x80000 - 0xfffff
  //
  local function bit expand_flash_address(int unsigned        address,
                                          output int unsigned rel_address,
                                          output              chip_mem_e mem_idx);
    // Do we fit in slot A?
    if (address < 'h80000) begin
      rel_address = address;
      mem_idx     = FlashBank0Data;
      return 1'b1;
    end

    // We didn't fit in slot A. Do we fit in slot B?
    if (address < 'hfffff) begin
      rel_address = address - 'h80000;
      mem_idx     = FlashBank1Data;
      return 1'b1;
    end

    // We have run out of slots. Set the indices to something invalid and return 0.
    rel_address = '1;
    mem_idx     = chip_mem_e'('1);
    return 1'b0;
  endfunction
endclass
