// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// pick a random mem address to inject parity errors and read it back,
// then check it returns d_error with all 1s data
class spi_device_mem_parity_vseq extends spi_device_common_vseq;
  `uvm_object_utils(spi_device_mem_parity_vseq)
  `uvm_object_new

  localparam int BytePerWord = 4;
  localparam int BitPerByte = 9;

  rand bit[BytePerWord-1:0][BitPerByte-1:0] flip_bits;

  // at least flip one bit and at most flip one bit per byte
  constraint flip_bits_c {
    flip_bits != 0;
    foreach (flip_bits[i]) $countones(flip_bits[i]) <= 1;
  }

  virtual task body();
    bit [TL_AW-1:0] offset = $urandom_range(0, (SRAM_SIZE / SRAM_WORD_SIZE) - 1);
    bit [TL_DW-1:0] data;
    logic [BitPerByte*BytePerWord-1:0] mem_data;
    string path = $sformatf("tb.dut.u_memory_2p.u_mem.gen_generic.u_impl_generic.mem[%0d]", offset);

    repeat (100) begin
      mem_wr(.ptr(ral.buffer), .offset(offset), .data($urandom));

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(flip_bits)
      // backdoor read and inject parity errors
      `DV_CHECK(uvm_hdl_read(path, mem_data));
      `DV_CHECK(uvm_hdl_deposit(path, mem_data ^ flip_bits));
      // frontdoor read to check it returns d_error
      tl_access(.addr(ral.buffer.get_offset() + (offset << 2)),
                .write(0),
                .data(data),
                .mask(get_rand_contiguous_mask()),
                .exp_err_rsp(1),
                // returned data is all 1s when it detects an error
                .check_exp_data(1),
                .exp_data({TL_DW{1'b1}}));
    end
  endtask
endclass : spi_device_mem_parity_vseq
