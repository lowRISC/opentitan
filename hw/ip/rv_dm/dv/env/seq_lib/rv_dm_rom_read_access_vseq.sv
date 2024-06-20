// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_rom_read_access_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_rom_read_access_vseq)
  `uvm_object_new

  task body();
    string         path;
    bit [31:0]     lower_mem_val;
    bit [31:0]     upper_mem_val;
    uvm_reg_data_t mem_val;
    uvm_reg_data_t rom_data;

    repeat (2) begin
      for (int i = 0; i < 20; i++) begin
        path = $sformatf("tb.dut.u_dm_top.i_dm_mem.gen_rom_snd_scratch.i_debug_rom.mem[%0d]", i);
        `DV_CHECK(uvm_hdl_read(path, rom_data))
        mem_rd(.ptr(tl_mem_ral.rom), .offset(i*2), .data(lower_mem_val));
        mem_rd(.ptr(tl_mem_ral.rom), .offset(i*2+1), .data(upper_mem_val));
        mem_val = {upper_mem_val, lower_mem_val};
        `DV_CHECK_EQ(mem_val, rom_data)
      end
    end
  endtask

endclass : rv_dm_rom_read_access_vseq
