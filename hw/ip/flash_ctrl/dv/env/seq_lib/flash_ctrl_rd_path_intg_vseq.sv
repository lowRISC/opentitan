// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence sends read and write traffic with or without tlul memory
// bus read path error injection.
// Error response will be sent to tl_agent(flash_ctrl_eflash_reg_block)
// with d_error=1.
class flash_ctrl_rd_path_intg_vseq extends flash_ctrl_rw_vseq;
  `uvm_object_utils(flash_ctrl_rd_path_intg_vseq)
  `uvm_object_new

  task body();
    string path1 = {"tb.dut.u_eflash.gen_flash_cores[0].u_core",
                    ".u_rd.u_bus_intg.data_intg_o[38]"};
    string path2 = {"tb.dut.u_eflash.gen_flash_cores[1].u_core",
                    ".u_rd.u_bus_intg.data_intg_o[38]"};

    `uvm_info(`gfn, "Assert read path err", UVM_LOW)
    `DV_CHECK(uvm_hdl_force(path1, 1'b1))
    `DV_CHECK(uvm_hdl_force(path2, 1'b1))
    cfg.scb_h.exp_tl_rsp_intg_err = 1;

    super.body();
    `uvm_info(`gfn, "Wait until all drain", UVM_LOW)
    cfg.clk_rst_vif.wait_clks(100);
    `DV_CHECK(uvm_hdl_release(path1))
    `DV_CHECK(uvm_hdl_release(path2))
    `uvm_info(`gfn, "Normal traffic START", UVM_LOW)
    cfg.scb_h.exp_tl_rsp_intg_err = 0;

    super.body();
  endtask

endclass
