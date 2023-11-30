// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dmi_failed_op_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_failed_op_vseq)

  `uvm_object_new

   constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
      uvm_reg_data_t data;
      uvm_reg_data_t rdata;
      data = $urandom_range(0,31);
      csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value(data));
      csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(data));
      csr_rd(.ptr(jtag_dtm_ral.dtmcs), .value(rdata));
      //checking busy error
      `DV_CHECK_EQ(3,get_field_val(jtag_dtm_ral.dtmcs.dmistat, rdata));//failing at this stage
      csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmireset), .value(1));
      csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata);
      `DV_CHECK_EQ(data,rdata);
  endtask

endclass

