// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run chip csr_rw sequence via JTAG RV_DM interface.
class chip_jtag_csr_rw_vseq extends chip_common_vseq;
  `uvm_object_utils(chip_jtag_csr_rw_vseq)

  `uvm_object_new

  virtual task pre_start();
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
    super.pre_start();
  endtask

  virtual task body();
    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");

    cfg.m_jtag_riscv_agent_cfg.allow_errors = 1;
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 0;

    run_common_vseq_wrapper(num_trans);
  endtask : body

  // A wrapper around dv_base_vseq::run_csr_vseq_wrapper that narrows models down to the main chip
  // register block. The JTAG agent reaches registers through the rv_dm system bus, which is a host
  // on the main crossbar only. The soc_dbg and soc_mbx register blocks sit on crossbars that only
  // the JTAG DTM and the SoC side can reach.
  virtual task run_csr_vseq_wrapper(int num_times = 1, dv_base_reg_block models[$] = {});
    if (models.size() > 0 && !(cfg.ral inside {models})) begin
      `uvm_fatal(`gfn, "Cannot run CSR vseq: models doesn't contain the main RAL.")
    end
    super.run_csr_vseq_wrapper(num_times, {cfg.ral});
  endtask

  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");
    if (!(models.size() == 1 && models[0] == cfg.ral) &&
        !(models.size() == 0 && ral_name == "chip_reg_block")) begin
      `uvm_fatal(`gfn, "JTAG access only works for the main register block.")
    end

    // JTAG cannot process outstanding access, so JTAG protocol will process one request at a time.
    // However, still set this variable to 1 to avoid spinwait timeout when sequence sends all csrs
    // transaction requests at .
    max_outstanding_accesses = 1;

    // Run 500 csrs at one sequence to avoid simulation timeout.
    super.run_csr_vseq(csr_test_type, 500, do_rand_wr_and_reset, models, ral_name);
  endtask

endclass
