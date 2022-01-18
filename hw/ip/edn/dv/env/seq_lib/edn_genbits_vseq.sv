// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_genbits_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_genbits_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
      m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  bit [edn_pkg::ENDPOINT_BUS_WIDTH - 1:0]       edn_bus[MAX_NUM_ENDPOINTS];
  bit [3:0]                                     acmd, clen, flags;
  bit [17:0]                                    glen;
  uint                                          num_requesters, num_requests,
                                                num_requests_q[$], endpoint_q[$];

  task body();
    super.body();

    // TODO: Test boot_mode, auto_req_mode

    // Wait for cmd_rdy
    csr_spinwait(.ptr(ral.sw_cmd_sts.cmd_rdy), .exp_data(1'b1));

    // Create/Send INS cmd
    acmd  = csrng_pkg::INS;
    flags = 4'h1;
    csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, acmd}));

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));

    // Determine which endpoints requesting
    for (int i = 0; i < cfg.num_endpoints; i++) begin
      endpoint_q.push_back(i);
    end
    endpoint_q.shuffle();
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_requesters,
                                       num_requesters inside { [1:cfg.num_endpoints] };)
    endpoint_q = endpoint_q[0:num_requesters - 1];

    // Calculate num_requests -> glen
    for (int i = 0; i < num_requesters; i++) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_requests,
                                         num_requests inside
                                             { [MIN_NUM_REQUESTS:MAX_NUM_REQUESTS] };
                                         num_requests % 4 == 0;)
      num_requests_q.push_back(num_requests);
      glen += num_requests/4;
    end

    // Load genbits_agent
    for (int i = 0; i < glen; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
      `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
      cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});
    end

    // Create/configure endpoint_pull sequences
    for (int i = 0; i < num_requesters; i++) begin
      m_endpoint_pull_seq[endpoint_q[i]] = push_pull_host_seq#(FIPS_ENDPOINT_BUS_WIDTH)::
          type_id::create($sformatf("m_endpoint_pull_seq[%0d]", endpoint_q[i]));
      m_endpoint_pull_seq[endpoint_q[i]].num_trans = num_requests_q[i];
    end

    // Create/Send GEN cmd
    acmd  = csrng_pkg::GEN;
    flags = 4'h0;
    csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, acmd}));

    // Start endpoint_pull sequences
    for (int i = 0; i < num_requesters; i++) begin
      automatic int j = i;
      fork
        begin
          m_endpoint_pull_seq[endpoint_q[j]].start
              (p_sequencer.endpoint_sequencer_h[endpoint_q[j]]);
        end
      join_none;
    end

    // Expect/Clear interrupt bit
    csr_spinwait(.ptr(ral.intr_state.edn_cmd_req_done), .exp_data(1'b1));
    check_interrupts(.interrupts((1 << CmdReqDone)), .check_set(1'b1));
  endtask

endclass
