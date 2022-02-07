// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_genbits_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_genbits_vseq)
  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
      m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  uint   num_requesters, num_requests, num_genbits, endpoint_q[$];

  task body();
    super.body();

    // Determine which endpoints are requesting
    for (int i = 0; i < cfg.num_endpoints; i++) begin
      endpoint_q.push_back(i);
    end
    endpoint_q.shuffle();
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_requesters,
                                       num_requesters inside { [1:cfg.num_endpoints] };)
    endpoint_q = endpoint_q[0:num_requesters - 1];

    for (int i = 0; i < num_requesters; i++) begin
      // Calculate num_requests -> glen
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_requests,
                                         num_requests inside
                                             { [cfg.min_num_requests:cfg.max_num_requests] };
                                         num_requests % 4 == 0;)
      num_genbits += num_requests/4;

      if ((i == 0) && (cfg.boot_req_mode == MuBi4True)) begin
        // TODO: Not hard-coded 4
        num_requests += cfg.num_boot_genbits * 4;
      end

      // Create/Configure endpoint_pull_seq
      m_endpoint_pull_seq[endpoint_q[i]] = push_pull_host_seq#(FIPS_ENDPOINT_BUS_WIDTH)::
          type_id::create($sformatf("m_endpoint_pull_seq[%0d]", endpoint_q[i]));
      m_endpoint_pull_seq[endpoint_q[i]].num_trans = num_requests;
    end

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

    if (cfg.auto_req_mode == MuBi4True) begin
      // TODO: Doesn't test functionality of max_num_reqs_between_reseeds register
      csr_wr(.ptr(ral.max_num_reqs_between_reseeds), .value(cfg.num_reqs_between_reseeds));
      wr_cmd(.cmd_type("reseed"), .acmd(csrng_pkg::RES), .clen(0), .flags(0), .glen(0));
      wr_cmd(.cmd_type("generate"), .acmd(csrng_pkg::GEN), .clen(0), .flags(4'hF),
             // .glen(MIN_GLEN));
             .glen(num_genbits));
    end

    // TODO: Make num_requests not 4*num_genbits
    if (cfg.boot_req_mode != MuBi4True) begin
      // Send instantiate cmd
      wr_cmd(.cmd_type("sw"), .acmd(csrng_pkg::INS), .clen(0), .flags(4'hF), .glen(0));
    end

    if (cfg.auto_req_mode != MuBi4True) begin
      // Send generate cmd
      wr_cmd(.cmd_type("sw"), .acmd(csrng_pkg::GEN), .clen(0), .flags(1), .glen(num_genbits));
    end

    if (cfg.auto_req_mode == MuBi4True) begin
      ral.ctrl.auto_req_mode.set(MuBi4False);
      csr_update(.csr(ral.ctrl));
    end
  endtask

endclass
