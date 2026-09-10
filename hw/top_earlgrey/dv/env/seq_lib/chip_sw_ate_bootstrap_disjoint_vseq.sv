// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test performs a the first two steps of a ROM bootstrap operation, i.e., NVM erase followed
// by a single page program operation. It then confirms NVM has been programmed, by backdoor
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
    // load up the contents of the firmware image into the NVM. That will only happen
    // if a SW image exists: make sure it does and fail quickly if not.
    if (!cfg.sw_images.exists(SwTypeTestSlotA)) begin
      `uvm_fatal(get_name(), "Slot A image doesn't exist.")
    end

    super.body();

    // Read the SW frames again into a local queue. This feels a little silly (because we did it in
    // the base class as well), but it's reasonably quick.
    sw_image = {cfg.sw_images[SwTypeTestSlotA], ".128.vmem"};
    read_sw_frames(sw_image, sw_byte_q, .word_size_bits(128));

    // Read back the programmed NVM data page to confirm it was programmed correctly.
    for (int a = 0; a < sw_byte_q.size; a += 4) begin
      bit [31:0] expected = {sw_byte_q[a + 3], sw_byte_q[a + 2],
                             sw_byte_q[a + 1], sw_byte_q[a + 0]};
      if (!check_nvm_word_32(a, expected)) num_errors++;
    end
    if (num_errors > 0) begin
      `uvm_error(get_name(),
                 $sformatf("Found %0d errors when checking programmed NVM", num_errors))
    end

    // Set test passed.
    assert_por_reset();
    override_test_status_and_finish(.passed(1'b1));
  endtask

  // This overrides a task in chip_sw_base_vseq
  //
  // We run the normal version *unless* the relevant range of byte_q happens to only contain 'hff.
  // If it does, there is no need to write the page: we know that we have just erased NVM to that
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

  // Do a backdoor read of a 32-bit word in NVM. On a match, return true. On a mismatch, generate
  // a uvm_error describing the mismatch and return false.
  //
  function bit check_nvm_word_32(int unsigned address, bit [31:0] expected);
    // RRAM backs the whole NVM data partition with one contiguous region (unlike flash, which
    // backed slots A and B with two separate physical banks), so the SW address maps onto it
    // directly and should never fall outside of it.
    chip_mem_e       mem_idx = RramData;
    logic [31:0]     actual;

    if (address >= cfg.mem_bkdr_util_h[mem_idx].get_size_bytes()) begin
      `uvm_error(get_name(),
                 $sformatf("Address 0x%0h is out of range for the RRAM model (mem_idx %0p).",
                           address, mem_idx))
      return 1'b0;
    end

    // Look up the associated backdoor and check that the NVM memory agrees.
    actual = cfg.mem_bkdr_util_h[mem_idx].read32(address);

    if (actual === expected) begin
      return 1'b1;
    end else begin
      `uvm_error(get_name(),
                 $sformatf({"NVM data mismatch at 0x%0h (mem_idx %0p). ",
                            "We expected 0x%0h but saw 0x%0h."},
                           address, mem_idx, expected, actual))
      return 1'b0;
    end
  endfunction
endclass
