// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A RV_DM jtag sequence to activate DM mode.
class jtag_riscv_dm_activation_seq extends jtag_riscv_base_seq;

  `uvm_object_utils_begin(jtag_riscv_dm_activation_seq)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_create_obj(REQ, req)
    start_item(req);

    `DV_CHECK_RANDOMIZE_WITH_FATAL(req, activate_rv_dm == 1;)

    finish_item(req);
    get_response(rsp);

    if (!cfg.allow_errors) begin
      `DV_CHECK_EQ(rsp.status, DmiNoErr, "jtag_csr_dm_activation failed!")
    end
  endtask

endclass
