// Copyright lowRISC contributors.
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

  task body();

    csr_wr(.ptr(ral.regwen), .value(ctrl_bit), .blocking(1));
    csr_wr(.ptr(ral.regwen), .value(~ctrl_bit), .blocking(1));
    csr_rd(.ptr(ral.regwen), .value(chk_bit), .blocking(1));

    if (chk_bit != ctrl_bit) begin
      `uvm_fatal(`gfn, $sformatf(" Was able to overwrite REGWEN after being set to 0"))
    end

    csr_rd(.ptr(ral.ctrl), .value(ctrl_int), .blocking(1));
    csr_wr(.ptr(ral.ctrl),
           .value(ctrl_int ^ 1'b1),
           .blocking(1));
    csr_rd(.ptr(ral.ctrl), .value(chk_int), .blocking(1));

    if (ctrl_int != chk_int) begin
      `uvm_fatal(`gfn, $sformatf(" Was able to overwrite CTRL with REGWEN being set to 0"))
    end

    csr_rd(.ptr(ral.err_code_test), .value(ctrl_int), .blocking(1));
    csr_wr(.ptr(ral.err_code_test),
           .value(ctrl_int ^ 1'b1),
           .blocking(1));
    csr_rd(.ptr(ral.err_code_test), .value(chk_int), .blocking(1));

    if (ctrl_int != chk_int) begin
      `uvm_fatal(`gfn, $sformatf(" Was able to overwrite ERR_CODE_TEST with REGWEN being set to 0"))
    end

  endtask : body

endclass : csrng_regwen_vseq
