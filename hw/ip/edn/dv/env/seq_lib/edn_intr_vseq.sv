// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test edn_cmd_req_done and edn_fatal_err interrupts fired as expected

class edn_intr_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_intr_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq;

  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  uint                                          endpoint_port;

  task test_edn_cmd_req_done();
    // Send INS cmd
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS), .clen(0), .flags(MuBi4False),
           .glen(0), .mode(edn_env_pkg::SwMode));

    // Send GEN cmd w/ GLEN 1 (request single genbits)
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4False),
           .glen(1), .mode(edn_env_pkg::SwMode));

    // Load expected genbits data
    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");
    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    // Request data
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endpoint_port,
                                       endpoint_port inside { [0:cfg.num_endpoints - 1] };)
    m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);
  endtask // test_edn_cmd_req_done

  task test_edn_fatal_err();
    string        path;
    string        fld_name;
    int           last_index;
    string        fifo_base_path;
    string        path_exts [4] = {"push", "full", "pop", "not_empty"};
    string        fifo_forced_paths [4];
    bit           fifo_forced_values [4] = {1'b1, 1'b1, 1'b1, 1'b0};

    // Turn off assertions
    $assertoff(0, "tb.dut.u_edn_core.u_prim_fifo_sync_rescmd.DataKnown_A");
    $assertoff(0, "tb.dut.u_edn_core.u_prim_fifo_sync_gencmd.DataKnown_A");
    cfg.edn_assert_vif.assert_off();

    // Enable intr_state
    csr_wr(.ptr(ral.intr_enable), .value(32'd3));

    fld_name = cfg.which_fatal_err.name();

    last_index = find_index("_", fld_name, "last");

    case (cfg.which_fatal_err) inside
      sfifo_rescmd_error, sfifo_gencmd_error: begin
        fifo_base_path = fld_name.substr(0, last_index-1);
        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.edn_vif.fifo_err_path(fifo_base_path, path_exts[i]);
        end
        force_all_fifo_errs(fifo_forced_paths, fifo_forced_values, path_exts,
                            ral.intr_state.edn_fatal_err, 1'b1, cfg.which_fifo_err);
      end
      edn_ack_sm_error, edn_main_sm_error: begin
        path = cfg.edn_vif.sm_err_path(fld_name.substr(0, last_index-1));
        force_path_err(path, 6'b0, ral.intr_state.edn_fatal_err, 1'b1);
      end
      edn_cntr_error: begin
        path = cfg.edn_vif.cntr_err_path();
        force_path_err(path, 6'b000001, ral.intr_state.edn_fatal_err, 1'b1);
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_fatal_err)

    // Turn assertions back on
    cfg.edn_assert_vif.assert_on();
  endtask // test_edn_fatal_err

  task body();
    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Test edn_cmd_req_done interrupt
    test_edn_cmd_req_done();

    // Test edn_fatal_err interrupt
    test_edn_fatal_err();

  endtask
endclass : edn_intr_vseq
