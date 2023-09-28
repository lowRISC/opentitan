// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_reg_reset_val_vseq extends mbx_base_vseq;

  rand int unsigned m_mbx_num;

  `uvm_object_utils(mbx_reg_reset_val_vseq)

  constraint mbx_num_c { m_mbx_num == 0; }

  function new(string name = "");
    super.new();
    do_mbx_init = 1'b0;
  endfunction: new

  task soc_reg_reset_val_check();
    bit [31:0] rd_data;

    `uvm_info(get_full_name(), "soc_reg_reset_val_check -- Start", UVM_DEBUG)

    // DOE Control Register
    csr_rd(m_mbx_soc_ral.m_mbxsoc_reg_block[m_mbx_num].mbxctl, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for mbxctl")

    // DOE Status Register
    csr_rd(m_mbx_soc_ral.m_mbxsoc_reg_block[m_mbx_num].mbxsts, rd_data);
    `DV_CHECK_EQ(rd_data, 1, "Reset value mismatch for mbxsts")

    // DOE Write Data Register
    csr_rd(m_mbx_soc_ral.m_mbxsoc_reg_block[m_mbx_num].mbxwrdat, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for mbxwrdat")

    // DOE Read Data Register
    csr_rd(m_mbx_soc_ral.m_mbxsoc_reg_block[m_mbx_num].mbxrddat, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for mbxrddat")

    `uvm_info(get_full_name(), "soc_reg_reset_val_check -- End", UVM_DEBUG)
  endtask: soc_reg_reset_val_check

  task core_reg_reset_val_check();
    bit [31:0] rd_data;

    `uvm_info(get_full_name(), "core_reg_reset_val_check -- Start", UVM_DEBUG)
    // DOE Control Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxctl, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for uarch mbxctl")

    // DOE Status Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxsts, rd_data);
    `DV_CHECK_EQ(rd_data, 1, "Reset value mismatch for uarch mbxsts")

    // DOE IBBASE Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxibbase, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for uarch mbxibbase")

    // DOE IBLIMIT Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxiblmit, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for uarch mbxiblmit")

    // DOE OBBASE Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxobbase, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for uarch mbxobbase")

    // DOE OBLIMIT Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxoblmit, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for uarch mbxoblmit")

    // DOE OBDWCNT Register
    csr_rd(ral.m_mbxhst_reg_block[m_mbx_num].mbxobdwcnt, rd_data);
    `DV_CHECK_EQ(rd_data, 0, "Reset value mismatch for uarch mbxobdwcnt")

    `uvm_info(get_full_name(), "core_reg_reset_val_check -- End", UVM_DEBUG)
  endtask: core_reg_reset_val_check

  task body();
    `uvm_info(get_full_name(), "body -- Start", UVM_DEBUG)
    super.body();

    // System Side
    soc_reg_reset_val_check();

    // Host Side
    core_reg_reset_val_check();

    `uvm_info(get_full_name(), "body -- End", UVM_DEBUG)
  endtask: body

endclass: mbx_reg_reset_val_vseq
