// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_data_integrity_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_data_integrity_vseq)

  `uvm_object_new

  virtual task body();
    bit [31:0] error_ram_address;
    bit [ 7:0] sw_error_ram_address[];

    // This sequence will trigger a fatal sec_cm failure.
    super.body();

    error_ram_address = ral.sram_ctrl_main_ram.default_map.get_base_addr() + 32'h0000_4000;

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the address thal will trigger an error when read.
    sw_error_ram_address = {<<byte{error_ram_address}};
    `uvm_info(`gfn, $sformatf("address 0x%x as bytes %p", error_ram_address, sw_error_ram_address),
              UVM_MEDIUM)
    sw_symbol_backdoor_overwrite("kErrorRamAddress", sw_error_ram_address);

    // And corrupt the data.
    `uvm_info(`gfn, $sformatf(
              "Corrupting memory at address 0x%x, for alert %0d", error_ram_address, 63),
              UVM_MEDIUM)
    main_sram_bkdr_write32(.addr(error_ram_address), .data('0), .flip_bits(39'h1001));
  endtask
endclass
