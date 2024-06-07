// Copyright lowRISC contributors (OpenTitan project).
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
    bit [TL_AW-1:0] ingress_sram_offset =
      (cfg.sram_ingress_start_addr - cfg.sram_egress_start_addr) >> 2;
    bit [TL_AW-1:0] offset = $urandom_range(0, (SRAM_INGRESS_SIZE / SRAM_WORD_SIZE) - 1);
    bit [TL_DW-1:0] data;
    logic [BitPerByte*BytePerWord-1:0] mem_data;
    // TODO: Add support for the gen_ram1r1w variant.
    string path_fmt =
      "tb.dut.u_spid_dpram.gen_ram2p.u_memory_2p.u_mem.mem[%0d]";
    string egress_path = $sformatf(path_fmt, offset);
    string ingress_path = $sformatf(path_fmt, ingress_sram_offset + offset);

    // Disable comparisons with the mirror values, since the egress area is
    // write-only, and the ingress area is read-only.
    cfg.en_scb_mem_chk = 0;

    repeat (100) begin
      // Write to the egress buffer to get the word with correct parity bits.
      mem_wr(.ptr(ral.egress_buffer), .offset(offset), .data($urandom));

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(flip_bits)
      // backdoor read and inject parity errors
      `DV_CHECK(uvm_hdl_read(egress_path, mem_data));
      `DV_CHECK(uvm_hdl_deposit(ingress_path, mem_data ^ flip_bits));
      // frontdoor read to check it returns d_error
      tl_access(.addr(ral.ingress_buffer.get_offset() + (offset << 2)),
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
