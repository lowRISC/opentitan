// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Randomly set dut.cfg_i and check this value is propagated to prim_generic_ram_1p.
class sram_ctrl_ram_cfg_vseq extends sram_ctrl_base_vseq;

  `uvm_object_utils(sram_ctrl_ram_cfg_vseq)
  `uvm_object_new

  virtual task body();
    prim_ram_1p_pkg::ram_1p_cfg_t src_ram_cfg, dst_ram_cfg;
    string src_path = "tb.dut.cfg_i";
    string dst_path = {"tb.dut.u_prim_ram_1p_scr.u_prim_ram_1p_adv.gen_ram_inst[0].",
                       "u_mem.cfg_i"};

    repeat (100) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(src_ram_cfg)
      `DV_CHECK(uvm_hdl_deposit(src_path, src_ram_cfg))
      #($urandom_range(1, 100) * 1ns);
      `DV_CHECK(uvm_hdl_read(dst_path, dst_ram_cfg))
      `DV_CHECK_CASE_EQ(src_ram_cfg, dst_ram_cfg)
    end
  endtask
endclass
