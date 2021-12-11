// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_genbits_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_genbits_vseq)

  `uvm_object_new

   push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
       m_endpoint_pull_seq[edn_env_pkg::MAX_NUM_ENDPOINTS];

  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  bit [edn_pkg::ENDPOINT_BUS_WIDTH - 1:0]       edn_bus[edn_env_pkg::MAX_NUM_ENDPOINTS];

  task body();
    // Wait for cmd_rdy
    csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));

    // Send INS cmd
    csr_wr(.ptr(ral.sw_cmd_req), .value(32'h1));

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));

    // Send GEN cmd w/ GLEN 8 (request single genbits)
    csr_wr(.ptr(ral.sw_cmd_req), .value(32'h8003));

    // Load expected genbits data
    for (int i = 0; i < edn_env_pkg::MAX_NUM_ENDPOINTS; i++) begin
        `uvm_info(`gfn, "Loop started", UVM_LOW)

        m_endpoint_pull_seq[i] = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
            create("m_endpoint_pull_seq[i]");
        `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
        `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
        cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    // Request data
        m_endpoint_pull_seq[i].start(p_sequencer.endpoint_sequencer_h[i]);

    end

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

endclass
