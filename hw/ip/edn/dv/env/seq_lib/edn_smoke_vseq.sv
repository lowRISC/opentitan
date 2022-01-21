// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_smoke_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_smoke_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  task body();
    super.body();

    m_endpoint_pull_seq[0] = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq[0]");

    // Verify boot_req_mode cmds, continue after disable
    if (cfg.boot_req_mode == MuBi4True) begin
      m_endpoint_pull_seq[0].num_trans = csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH;
      m_endpoint_pull_seq[0].start(p_sequencer.endpoint_sequencer_h[0]);
    end

    // Wait for cmd_rdy
    csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));

    // Create/Send INS cmd
    acmd  = csrng_pkg::INS;
    csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, acmd}));

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));

    // Load genbits_agent
    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    // Wait for cmd_rdy
    csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));

    // Create/Send GEN cmd
    acmd  = csrng_pkg::GEN;
    glen  = 'h1;
    csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, acmd}));

    // Request data
    m_endpoint_pull_seq[0] = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq[0]");
    m_endpoint_pull_seq[0].num_trans = csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH;
    m_endpoint_pull_seq[0].start(p_sequencer.endpoint_sequencer_h[0]);

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

endclass
