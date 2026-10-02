// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_cfg_regwen_vseq extends entropy_src_base_vseq;

  `uvm_object_utils(entropy_src_cfg_regwen_vseq)

  `uvm_object_new

  bit ctrl_bit        = 0;
  bit chk_bit         = 0;
  int ctrl_mod_enable = 0;
  int mod_enable_chk  = 0;

  task body();

    csr_wr(.ptr(ral.sw_regupd), .value(ctrl_bit), .blocking(1));
    csr_wr(.ptr(ral.sw_regupd), .value(~ctrl_bit), .blocking(1));
    csr_rd(.ptr(ral.sw_regupd), .value(chk_bit), .blocking(1));

    if (chk_bit != ctrl_bit) begin
      `uvm_fatal(`gfn, $sformatf(" Was able to overwrite SW_REGUPD after being set to 0"))
    end
  endtask // body

endclass : entropy_src_cfg_regwen_vseq
