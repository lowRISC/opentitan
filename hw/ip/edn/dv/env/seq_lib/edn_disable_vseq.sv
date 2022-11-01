// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_disable_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_disable_vseq)
  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
      m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  uint   num_requesters, num_ep_reqs, num_cs_reqs, wait_disable;

  string   enable_path, boot_path, auto_path;

  task body();
    super.body();

    enable_path = "tb.dut.u_edn_core.mubi_edn_enable";
    boot_path   = "tb.dut.u_edn_core.mubi_boot_req_mode";
    auto_path   = "tb.dut.u_edn_core.mubi_auto_req_mode";

    fork
      begin
        // Random delay, disable edn
        // TODO: Modify min/max wait_disable values to hit all states
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wait_disable,
                                           wait_disable inside
                                           { [80:100] };)
        cfg.clk_rst_vif.wait_clks(wait_disable);
        // Disable edn, boot_req_mode, auto_req_mode
        `DV_CHECK(uvm_hdl_deposit(enable_path, MuBi4False));
        `DV_CHECK(uvm_hdl_deposit(boot_path, MuBi4False));
        `DV_CHECK(uvm_hdl_deposit(auto_path, MuBi4False));
        cfg.clk_rst_vif.wait_clks(10);
        // Enable edn
        `DV_CHECK(uvm_hdl_deposit(enable_path, MuBi4True));
      end
    join_none

    num_requesters = cfg.num_endpoints;
    num_cs_reqs    = cfg.num_endpoints;
    num_ep_reqs    = num_cs_reqs * csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH;

    for (int i = 0; i < num_requesters; i++) begin
      // Create/Configure/Start endpoint_pull_seq
      m_endpoint_pull_seq[i] = push_pull_host_seq#(FIPS_ENDPOINT_BUS_WIDTH)::
          type_id::create($sformatf("m_endpoint_pull_seq[%0d]", i));
      m_endpoint_pull_seq[i].num_trans = num_ep_reqs;
    end

    // Start endpoint_pull sequences
    for (int i = 0; i < num_requesters; i++) begin
      automatic int j = i;
      fork
        begin
          m_endpoint_pull_seq[j].start
              (p_sequencer.endpoint_sequencer_h[j]);
        end
      join_none;
    end
  endtask

endclass
