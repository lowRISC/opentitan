// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_jtag_dtm_hard_reset_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_hard_reset_vseq)

  `uvm_object_new

  // Write value over DMI to abstractdata[0]
  task set_abstractdata0(bit [31:0] value);
    csr_wr(.ptr(jtag_dmi_ral.abstractdata[0]), .value(value));
  endtask

  // Write value over DMI to progbuf[0]
  task set_progbuf0(bit [31:0] value);
    csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value(value));
  endtask

  // Read abstractdata[0] over DMI and check it has the expected value
  task check_abstractdata0(bit [31:0] expected);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dmi_ral.abstractdata[0]), .value(rdata));
    `DV_CHECK_EQ(rdata, expected)
  endtask

  // Read progbuf[0] over DMI and check it has the expected value
  task check_progbuf0(bit [31:0] expected);
    uvm_reg_data_t rdata;
    csr_rd(.ptr(jtag_dmi_ral.progbuf[0]), .value(rdata));
    `DV_CHECK_EQ(rdata, expected)
  endtask

  task body();
    uvm_reg_data_t abstractdata_val = $urandom, progbuf_val = $urandom;

    // Write to a couple of registers over DMI and then read their values back to check they have
    // been set as expected.
    set_abstractdata0(abstractdata_val);
    set_progbuf0(progbuf_val);
    check_abstractdata0(abstractdata_val);
    check_progbuf0(progbuf_val);

    // Perform the hard reset
    csr_wr(.ptr(jtag_dtm_ral.dtmcs.dmihardreset), .value(1));

    // Read the registers again, checking that they haven't lost their values
    check_abstractdata0(abstractdata_val);
    check_progbuf0(progbuf_val);
  endtask : body
endclass : rv_dm_jtag_dtm_hard_reset_vseq
