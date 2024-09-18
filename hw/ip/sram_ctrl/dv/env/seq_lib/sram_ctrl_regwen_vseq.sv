// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests exec_regwen, ctrl_regwen, and readback_regwen as well as their related
// CSRs.
// ctrl_regwen related CSRs (renew_scr_key and init) are excluded from CSR tests as they affect
// other CSRs.
// readback_regwen related CSRs are excluded from CSR tests as they affect other CSRs.
// exec_regwen and its related CSRs are tested in CSR tests, but this `exec` feature relates to
// other sram inputs (en_sram_ifetch and hw_debug_en), so also test it in this vseq.
class sram_ctrl_regwen_vseq extends sram_ctrl_executable_vseq;

  `uvm_object_utils(sram_ctrl_regwen_vseq)
  `uvm_object_new

  int readback_reg_val = 0;
  rand mubi4_t readback_en;

  task req_mem_init(bit wait_done);
    super.req_mem_init(wait_done);
    `DV_CHECK_RANDOMIZE_FATAL(ral.exec_regwen)
    csr_update(ral.exec_regwen);
    `DV_CHECK_RANDOMIZE_FATAL(ral.ctrl_regwen)
    csr_update(ral.ctrl_regwen);
    `DV_CHECK_RANDOMIZE_FATAL(ral.readback_regwen)
    csr_update(ral.readback_regwen);
    `uvm_info(`gfn, $sformatf("exec_regwen: %0d, ctrl_regwen: %0d, readback_regwen: %0d",
                              `gmv(ral.exec_regwen), `gmv(ral.ctrl_regwen),
                              `gmv(ral.readback_regwen)), UVM_MEDIUM)

    // req_mem_init in base seq only write 'b11 to this CSR
    // do some dummy write here to gain 100% coverage for regwen
    if (`gmv(ral.ctrl_regwen)) begin
      // when regwen=1, writing 0 to ctrl won't affect anything.
      csr_wr(.ptr(ral.ctrl), .value(0));
    end else begin
      // when regwen=0, writing any value to ctrl won't affect anything.
      csr_wr(.ptr(ral.ctrl), .value($urandom));
    end
    // regwen coverage sample happens at read. ctrl is WO, so it always returns 0.
    csr_rd_check(.ptr(ral.ctrl), .compare_value(0));

    // Check readback_regwen.
    if (`gmv(ral.readback_regwen)) begin
      // when regwen=1, disable the readback feature.
      csr_wr(.ptr(ral.readback), .value(MuBi4False));
      // regwen coverage sample happens at read.
      csr_rd(.ptr(ral.readback), .value(readback_reg_val));
    end else begin
      // when regwen=0, writing any value to readback won't affect anything.
      csr_rd(.ptr(ral.readback), .value(readback_reg_val));
      csr_wr(.ptr(ral.readback), .value($urandom));
      csr_rd_check(.ptr(ral.readback), .compare_value(readback_reg_val));
    end
  endtask

endclass
