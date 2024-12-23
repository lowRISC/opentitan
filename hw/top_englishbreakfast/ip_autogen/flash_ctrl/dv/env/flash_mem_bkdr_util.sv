// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Extends mem_bkdr_util to support 2 levels of ECC required for flash.
class flash_mem_bkdr_util extends mem_bkdr_util;

  // Initialize the class instance - reuse the base class' new.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme,
               int extra_bits_per_subword = 0, int unsigned system_base_addr = 0);
    super.new(.name(name), .path(path), .depth(depth), .n_bits(n_bits),
              .err_detection_scheme(err_detection_scheme),
              .extra_bits_per_subword(extra_bits_per_subword),
              .system_base_addr(system_base_addr));
    // Error detection scheme is assumed to be 76_68, otherwise, the overrides below won't work.
    `DV_CHECK_EQ_FATAL(err_detection_scheme, mem_bkdr_util_pkg::EccHamming_76_68)
  endfunction

  // Flash has 2 levels of ECC - first on bits 63:0 applied to bits 71:64.
  virtual function uvm_hdl_data_t get_ecc_computed_data(uvm_hdl_data_t data);
    data = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
    return super.get_ecc_computed_data(data);
  endfunction

  // Randomize the memory with correct ECC.
  virtual function void randomize_mem();
    `uvm_info(`gfn, "Randomizing flash mem contents", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      uvm_hdl_data_t data;
      `DV_CHECK_STD_RANDOMIZE_FATAL(data, "Randomization failed!", path)
      data = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
      data = get_ecc_computed_data(data);
      write(i * bytes_per_word, data);
    end
  endfunction

endclass
