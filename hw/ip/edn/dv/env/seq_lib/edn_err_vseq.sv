// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test ERR_CODE fields asserted as expected, as well as the ERR_CODE_TEST register

class edn_err_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_err_vseq)

  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)   m_endpoint_pull_seq;

  bit [csrng_pkg::GENBITS_BUS_WIDTH - 1:0]      genbits;
  bit [entropy_src_pkg::FIPS_BUS_WIDTH - 1:0]   fips;
  bit [edn_pkg::ENDPOINT_BUS_WIDTH - 1:0]       edn_bus[MAX_NUM_ENDPOINTS];
  uint                                          endpoint_port;

  task body();
    bit [5:0]     err_code_test_bit;
    string        path, path1, path2;
    bit           value1, value2;
    string        fifo_name;
    int           first_index, last_index;
    string        fifo_base_path;
    string        path_exts [4] = {"push", "full", "pop", "not_empty"};
    string        fifo_forced_paths [4];
    bit           fifo_forced_values [4] = {1'b1, 1'b1, 1'b1, 1'b0};
    string        fifo_err_path [2][string];
    bit           fifo_err_value [2][string];
    string        path_key;
    string        reg_name, fld_name;
    uvm_reg       csr;
    uvm_reg_field fld;
    bit [31:0]    backdoor_err_code_val;

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Turn off assertions
    $assertoff(0, "tb.dut.u_edn_core.u_prim_fifo_sync_rescmd.DataKnown_A");
    $assertoff(0, "tb.dut.u_edn_core.u_prim_fifo_sync_gencmd.DataKnown_A");
    cfg.edn_assert_vif.assert_off();

    // Create background thread that writes the Instantiate and Generate commands to the SW command
    // register.
    fork
      begin
        // Send INS cmd
        wr_cmd(.cmd_type("sw"), .acmd(csrng_pkg::INS), .clen(0), .flags(MuBi4False), .glen(0));

        // Send GEN cmd w/ GLEN 1 (request single genbits)
        wr_cmd(.cmd_type("sw"), .acmd(csrng_pkg::GEN), .clen(0), .flags(MuBi4False), .glen(1));
      end
    join_none

    // Load genbits data
    m_endpoint_pull_seq = push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)::type_id::
        create("m_endpoint_pull_seq");
    `DV_CHECK_STD_RANDOMIZE_FATAL(fips)
    `DV_CHECK_STD_RANDOMIZE_FATAL(genbits)
    cfg.m_csrng_agent_cfg.m_genbits_push_agent_cfg.add_h_user_data({fips, genbits});

    // Create background thread that does endpoint requests.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endpoint_port,
                                       endpoint_port inside { [0:cfg.num_endpoints - 1] };)
    fork
      m_endpoint_pull_seq.start(p_sequencer.endpoint_sequencer_h[endpoint_port]);
    join_none

    reg_name = "err_code";
    csr = ral.get_reg_by_name(reg_name);
    fld_name = cfg.which_err_code.name();

    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");

    case (cfg.which_err_code) inside
      sfifo_rescmd_err, sfifo_gencmd_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_base_path = fld_name.substr(0, last_index-1);

        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.edn_vif.fifo_err_path(fifo_base_path, path_exts[i]);
        end
        force_all_fifo_errs(fifo_forced_paths, fifo_forced_values, path_exts, fld,
                            1'b1, cfg.which_fifo_err);
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      edn_ack_sm_err, edn_main_sm_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.edn_vif.sm_err_path(fld_name.substr(0, last_index-1));
        force_path_err(path, 6'b0, fld, 1'b1);
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      edn_cntr_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.edn_vif.cntr_err_path();
        force_path_err(path, 6'b000001, fld, 1'b1);
        // Verify EDN.MAIN_SM.CTR.LOCAL_ESC
        csr_rd_check(.ptr(ral.err_code.edn_cntr_err), .compare_value(1'b1));
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      fifo_write_err, fifo_read_err, fifo_state_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_name = cfg.which_fifo.name();
        path_key = fld_name.substr(first_index+1, last_index-1);

        path1 = cfg.edn_vif.fifo_err_path(fifo_name, fifo_err_path[0][path_key]);
        path2 = cfg.edn_vif.fifo_err_path(fifo_name, fifo_err_path[1][path_key]);
        value1 = fifo_err_value[0][path_key];
        value2 = fifo_err_value[1][path_key];
        force_fifo_err(path1, path2, value1, value2, fld, 1'b1);
        if (cfg.en_cov) begin
          csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
          cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
        end
      end
      sfifo_rescmd_err_test, sfifo_gencmd_err_test, edn_ack_sm_err_test, edn_main_sm_err_test,
      edn_cntr_err_test, fifo_write_err_test, fifo_read_err_test, fifo_state_err_test: begin
        fld = csr.get_field_by_name(fld_name.substr(0, last_index-1));
        err_code_test_bit = fld.get_lsb_pos();
        csr_wr(.ptr(ral.err_code_test.err_code_test), .value(err_code_test_bit));
        cfg.clk_rst_vif.wait_clks(50);
        csr_rd_check(.ptr(fld), .compare_value(1'b1));
        if (cfg.which_err_code == edn_cntr_err_test) begin
          // Verify EDN.MAIN_SM.CTR.LOCAL_ESC
          csr_rd_check(.ptr(ral.err_code.edn_main_sm_err), .compare_value(1'b1));
          if (cfg.en_cov) begin
            csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
            cov_vif.cg_error_sample(.err_code(backdoor_err_code_val));
          end
          // Clear interrupt_enable
          csr_wr(.ptr(ral.intr_enable), .value(32'd0));
          ral.ctrl.edn_enable.set(prim_mubi_pkg::MuBi4False);
          ral.ctrl.cmd_fifo_rst.set(prim_mubi_pkg::MuBi4True);
          csr_update(.csr(ral.ctrl));
          // Expect/Clear interrupt bit
          check_interrupts(.interrupts((1 << FifoErr)), .check_set(1'b1));
        end
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_err_code)

    // Turn assertions back on
    cfg.edn_assert_vif.assert_on();
  endtask

endclass : edn_err_vseq
