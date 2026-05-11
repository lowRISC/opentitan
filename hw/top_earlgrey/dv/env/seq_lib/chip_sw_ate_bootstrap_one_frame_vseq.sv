// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test performs the first two steps of a ROM bootstrap operation, i.e., flash erase followed
// by a single page program operation. It then reads the first data page through a backdoor to check
// this has been programmed.

class chip_sw_ate_bootstrap_one_frame_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ate_bootstrap_one_frame_vseq)
  `uvm_object_new

  local function automatic void _check_flash_data_page(input integer address,
                                                       input integer expected);
    logic [TL_DW-1:0] actual;
    actual = cfg.mem_bkdr_util_h[FlashBank0Data].read32(address);
    `DV_CHECK_EQ(actual, expected)
  endfunction

  virtual task body();
    int unsigned num_errors;
    string       sw_image;
    byte         sw_byte_q[$];
    int unsigned SPI_FLASH_PAGE_SIZE = 256;

    // Do the standard setup, including loading up the flash image with spi_device_load_bootstrap.
    //
    // This sequence won't actually load the whole image (see the way we've overridden
    // spi_write_flash_stream)
    super.body();

    // Read the SW frames again into a local queue. This feels a little silly (because we did it in
    // the base class as well), but it's reasonably quick.
    sw_image = {cfg.sw_images[SwTypeTestSlotA], ".64.vmem"};
    read_sw_frames(sw_image, sw_byte_q);

    // Do a backdoor read to check that the first page of flash (which should have been loaded in
    // super.body) has indeed been loaded.
    `uvm_info(`gfn, $sformatf("Checking page program succeeded\n"), UVM_LOW);
    for (int a = 0; a < SPI_FLASH_PAGE_SIZE; a += 4) begin
      bit [31:0] expected = {sw_byte_q[a+3], sw_byte_q[a+2], sw_byte_q[a+1], sw_byte_q[a+0]};
      if (!check_flash_word_32(a, expected)) num_errors++;
    end
    if (num_errors > 0) begin
      `uvm_error(get_name(),
                 $sformatf("Found %0d errors in first page of programmed flash", num_errors))
    end

    // Set test passed.
    assert_por_reset();
    if (!num_errors) override_test_status_and_finish(.passed(1'b1));
  endtask

  // An override of chip_sw_base_vseq::spi_write_flash_stream.
  //
  // We only actually want to write a single page (the first one), so we do this by discarding
  // everything after the first page_size bytes in the queue.
  protected virtual task spi_write_flash_stream(const ref byte byte_q[$],
                                                int unsigned page_size);
    // Discard the later items in the queue
    byte page_bytes[$];
    int unsigned new_size = (byte_q.size() > page_size) ? page_size : byte_q.size();
    page_bytes = byte_q[0 : new_size - 1];

    super.spi_write_flash_stream(page_bytes, page_size);
  endtask

  // Do a backdoor read of a 32-bit word from the first bank of flash. On a match, return true. On a
  // mismatch, generate a uvm_error describing the mismatch and return false.
  //
  local function bit check_flash_word_32(int unsigned address, bit [31:0] expected);
    logic [31:0]     actual = cfg.mem_bkdr_util_h[FlashBank0Data].read32(address);

    if (actual === expected) begin
      return 1'b1;
    end else begin
      `uvm_error(get_name(),
                 $sformatf({"Flash data mismatch at 0x%0h (in FlashBank0Data). ",
                            "We expected 0x%0h but saw 0x%0h."},
                           address, expected, actual))
      return 1'b0;
    end
  endfunction

endclass : chip_sw_ate_bootstrap_one_frame_vseq
