// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verify the countermeasure(s) CONFIG.REGWEN.

class csrng_regwen_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_regwen_vseq)

  `uvm_object_new

  bit ctrl_bit        = 0;
  bit chk_bit         = 0;
  int ctrl_int        = 0;
  int chk_int         = 0;

  rand bit [NUM_HW_APPS:0] int_state_read_enable;
  bit [NUM_HW_APPS:0] chk_int_state_read_enable;

  task body();

    // REGWEN
    csr_wr(.ptr(ral.regwen), .value(ctrl_bit), .blocking(1));
    csr_wr(.ptr(ral.regwen), .value(~ctrl_bit), .blocking(1));
    csr_rd(.ptr(ral.regwen), .value(chk_bit), .blocking(1));

    if (chk_bit != ctrl_bit) begin
      `uvm_fatal(`gfn, "Was able to overwrite REGWEN after being set to 0")
    end

    csr_rd(.ptr(ral.ctrl), .value(ctrl_int), .blocking(1));
    csr_wr(.ptr(ral.ctrl),
           .value(ctrl_int ^ 1'b1),
           .blocking(1));
    csr_rd(.ptr(ral.ctrl), .value(chk_int), .blocking(1));

    if (ctrl_int != chk_int) begin
      `uvm_fatal(`gfn, "Was able to overwrite CTRL with REGWEN being set to 0")
    end

    csr_rd(.ptr(ral.err_code_test), .value(ctrl_int), .blocking(1));
    csr_wr(.ptr(ral.err_code_test),
           .value(ctrl_int ^ 1'b1),
           .blocking(1));
    csr_rd(.ptr(ral.err_code_test), .value(chk_int), .blocking(1));

    if (ctrl_int != chk_int) begin
      `uvm_fatal(`gfn, "Was able to overwrite ERR_CODE_TEST with REGWEN being set to 0")
    end

    // INT_STATE_READ_ENABLE_REGWEN
    csr_rd(.ptr(ral.int_state_read_enable_regwen), .value(chk_bit), .blocking(1));
    if (chk_bit == 1'b1) begin
      // The register is still writeable. So let's do some writes before disabling write access.
      `uvm_info(`gfn,
          $sformatf("Testing INT_STATE_READ_ENABLE[_REGWEN] with value 0x%x",
              int_state_read_enable),
          UVM_MEDIUM);
      csr_wr(.ptr(ral.int_state_read_enable), .value(int_state_read_enable), .blocking(1));
      csr_rd(.ptr(ral.int_state_read_enable), .value(chk_int_state_read_enable), .blocking(1));
      if (chk_int_state_read_enable != int_state_read_enable) begin
        `uvm_fatal(`gfn, "Was unable to write INT_STATE_READ_ENABLE")
      end
      csr_wr(.ptr(ral.int_state_read_enable), .value(~int_state_read_enable), .blocking(1));
      csr_rd(.ptr(ral.int_state_read_enable), .value(chk_int_state_read_enable), .blocking(1));
      if (chk_int_state_read_enable != ~int_state_read_enable) begin
        `uvm_fatal(`gfn, "Was unable to flip INT_STATE_READ_ENABLE")
      end

      csr_wr(.ptr(ral.int_state_read_enable_regwen), .value(1'b0), .blocking(1));
      csr_rd(.ptr(ral.int_state_read_enable_regwen), .value(chk_bit), .blocking(1));
      if (chk_bit != 1'b0) begin
        `uvm_fatal(`gfn, "Was unable to set INT_STATE_READ_ENABLE_REGWEN to 0")
      end
    end

    csr_rd(.ptr(ral.int_state_read_enable), .value(chk_int_state_read_enable), .blocking(1));
    int_state_read_enable = ~chk_int_state_read_enable;
    `uvm_info(`gfn,
        $sformatf("Testing INT_STATE_READ_ENABLE[_REGWEN] with value 0x%x", int_state_read_enable),
        UVM_MEDIUM);
    csr_wr(.ptr(ral.int_state_read_enable), .value(int_state_read_enable), .blocking(1));
    csr_rd(.ptr(ral.int_state_read_enable), .value(chk_int_state_read_enable), .blocking(1));
    if (chk_int_state_read_enable == int_state_read_enable) begin
      `uvm_fatal(`gfn,
          "Was able to flip INT_STATE_READ_ENABLE with INT_STATE_READ_ENABLE_REGWEN set to 0")
    end

    csr_wr(.ptr(ral.int_state_read_enable_regwen), .value(1'b1), .blocking(1));
    csr_rd(.ptr(ral.int_state_read_enable_regwen), .value(chk_bit), .blocking(1));
    if (chk_bit == 1'b1) begin
      `uvm_fatal(`gfn, "Was able to put INT_STATE_READ_ENABLE_REGWEN back to 1")
    end

    super.body();

  endtask : body

endclass : csrng_regwen_vseq
