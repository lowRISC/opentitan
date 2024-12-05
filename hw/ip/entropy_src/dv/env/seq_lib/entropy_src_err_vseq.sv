// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test all ERR_CODE fields are asserted as expected, as well as the ERR_CODE_TEST register

`define PATH1 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_entropy_fips_en
`define PATH2 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_entropy_data_reg_en
`define PATH3 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_entropy_module_en
`define PATH4 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_rng_bit_en
`define PATH5 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_fw_ov_mode
`define PATH6 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_fw_ov_entropy_insert
`define PATH7 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_route
`define PATH8 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_type
`define PATH9 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_enable
`define PATH10 \
    tb.dut.u_entropy_src_core.u_prim_mubi4_sync_es_enable_pulse
`define CORE \
    tb.dut.u_entropy_src_core
`define SHA3 \
    u_sha3.u_keccak.u_round_count
`define REPCNT \
    u_entropy_src_repcnt_ht.u_prim_max_tree_rep_cntr_max
`define BUCKET \
    u_entropy_src_bucket_ht.u_prim_max_tree_bin_cntr_max

class entropy_src_err_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_err_vseq)

  `uvm_object_new

   push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)          m_rng_push_seq;

  task body();
    bit [5:0]        err_code_test_bit;
    string           path, path1, path2;
    bit              value, value1, value2;
    string           fifo_name, path_name;
    int              first_index, last_index;
    string           fifo_base_path;
    string           path_exts [4] = {"push", "full", "pop", "not_empty"};
    string           fifo_forced_paths [4];
    bit              fifo_forced_values [4] = {1'b1, 1'b1, 1'b0, 1'b1};
    string           fifo_err_path [2][string];
    bit              fifo_err_value [2][string];
    string           path_key;
    string           reg_name, fld_name;
    uvm_reg          csr;
    uvm_reg_field    fld;

    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Enable interrupts for fatal errors.
    csr_wr(.ptr(ral.intr_enable.es_fatal_err), .value(1'b1), .predict(1'b1));

    // Turn on module_enable
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4True));

    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
         create("m_rng_push_seq");
    m_rng_push_seq.num_trans = entropy_src_pkg::CSRNG_BUS_WIDTH/entropy_src_pkg::RNG_BUS_WIDTH;
    run_rng_host_seq(m_rng_push_seq);

    cfg.clk_rst_vif.wait_clks(100);

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full", "cntr": "int_err"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1, "cntr": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    reg_name = "err_code";
    csr = ral.get_reg_by_name(reg_name);
    fld_name = cfg.which_err_code.name();

    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");
    fifo_base_path = fld_name.substr(0, last_index-1);

    foreach (path_exts[i]) begin
      fifo_forced_paths[i] = cfg.entropy_src_path_vif.fifo_err_path(fifo_base_path, path_exts[i]);
    end

    // Turn off assertions that we expect to trigger by the errors that we inject in this vseq.
    assert_off_err();

    case (cfg.which_err_code) inside
      sfifo_esrng_err, sfifo_distr_err, sfifo_observe_err, sfifo_esfinal_err: begin
        path_name = cfg.which_fifo_err.name();

        path1 = cfg.entropy_src_path_vif.fifo_err_path(fifo_base_path,
                                                       fifo_err_path[0][path_name]);
        path2 = cfg.entropy_src_path_vif.fifo_err_path(fifo_base_path,
                                                       fifo_err_path[1][path_name]);
        value1 = fifo_err_value[0][path_name];
        value2 = fifo_err_value[1][path_name];

        fld = csr.get_field_by_name(fld_name);

        if (cfg.which_err_code == sfifo_esrng_err && cfg.which_fifo_err == write) begin
          force_fifo_err_exception(fifo_forced_paths, fifo_forced_values, fld, 1'b1);
        end else begin
          force_fifo_err(path1, path2, value1, value2, fld, 1'b1);
        end
        cov_vif.cg_fifo_err_sample(cfg.which_fifo_err, cfg.which_fifo);
      end
      es_ack_sm_err, es_main_sm_err: begin
        path = cfg.entropy_src_path_vif.sm_err_path(fld_name.substr(first_index+1, last_index-1));

        fld = csr.get_field_by_name(fld_name);

        force_path_err(path, 16'b0, fld, 1'b1);
        cov_vif.cg_sm_err_sample(fld_name == "es_ack_sm_err", fld_name == "es_main_sm_err");
      end
      es_cntr_err: begin
        logic [entropy_src_ack_sm_pkg::StateWidth-1:0] sm_state;
        string sm_state_path = cfg.entropy_src_path_vif.sm_err_path("ack_sm");
        fld = csr.get_field_by_name(fld_name);
        case (cfg.which_cntr)
          window_cntr: begin // window counter
            window_cntr_err_test(fld);
          end
          repcnt_ht_cntr: begin // repcnt ht test counter
            repcnt_ht_cntr_test(m_rng_push_seq, fld);
          end
          repcnts_ht_cntr: begin // repcnts ht test counter
            repcnts_ht_cntr_test(m_rng_push_seq, fld);
          end
          adaptp_ht_cntr: begin // adaptive proportion test counter
            adaptp_ht_cntr_test(m_rng_push_seq, fld);
          end
          bucket_ht_cntr: begin // Bucket test counter
            bucket_ht_cntr_test(m_rng_push_seq, fld);
          end
          markov_ht_cntr: begin // Markov test counter
            markov_ht_cntr_test(m_rng_push_seq, fld);
          end
          default: begin
            `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
          end
        endcase // case (cfg.which_cntr)
        cov_vif.cg_cntr_err_sample(cfg.which_cntr, cfg.which_cntr_replicate, cfg.which_bin);
        // Check that the `entropy_src_ack_sm` FSM, which observes the errors of the faulted
        // counter, has entered the error state.
        `DV_CHECK(uvm_hdl_read(sm_state_path, sm_state))
        `DV_CHECK_EQ(sm_state, entropy_src_ack_sm_pkg::Error)
      end
      fifo_read_err, fifo_state_err: begin
        fifo_name = cfg.which_fifo.name();
        path_key = fld_name.substr(first_index+1, last_index-1);

        path1 = cfg.entropy_src_path_vif.fifo_err_path(fifo_name, fifo_err_path[0][path_key]);
        path2 = cfg.entropy_src_path_vif.fifo_err_path(fifo_name, fifo_err_path[1][path_key]);
        value1 = fifo_err_value[0][path_key];
        value2 = fifo_err_value[1][path_key];

        fld = csr.get_field_by_name(fld_name);

        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.entropy_src_path_vif.fifo_err_path("sfifo_esrng",
                                                                        path_exts[i]);
        end
        force_fifo_err(path1, path2, value1, value2, fld, 1'b1);
        cov_vif.cg_fifo_err_sample(cfg.which_fifo_err, cfg.which_fifo);
      end
      fifo_cntr_err: begin
        fifo_name = cfg.which_fifo.name();
        path_key = fld_name.substr(first_index+1, last_index-1);

        path = cfg.entropy_src_path_vif.fifo_err_path(fifo_name, fifo_err_path[0][path_key]);
        value = fifo_err_value[0][path_key];

        fld = csr.get_field_by_name({cfg.which_fifo.name(), "_err"});
        force_path_err(path, value, fld, 1'b1);
        // TODO(#23988): uncomment the following lines.
        // // Additionally check if FIFO_STATE_ERR is set.
        // fld = csr.get_field_by_name("fifo_state_err");
        // csr_rd_check(.ptr(fld), .compare_value(1'b1));
        cov_vif.cg_fifo_err_sample(cfg.which_fifo_err, cfg.which_fifo);
      end
      sfifo_esrng_err_test, sfifo_distr_err_test, sfifo_observe_err_test, sfifo_esfinal_err_test,
      es_ack_sm_err_test, es_main_sm_err_test, es_cntr_err_test,
      fifo_read_err_test, fifo_state_err_test: begin
        // First turn off module_enable to write registers
        csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
        // Get the register field name
        fld = csr.get_field_by_name(fifo_base_path);

        err_code_test_bit = fld.get_lsb_pos();
        csr_wr(.ptr(ral.err_code_test.err_code_test), .value(err_code_test_bit));
        // Turn on module_enable
        csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4True));
        csr_spinwait(.ptr(fld), .exp_data(1'b1));
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_err_code)

    // Expect/Clear interrupt bit for fatal errors.
    check_interrupts(.interrupts((1 << FatalErr)), .check_set(1'b1));
    // Disable entropy_src
    csr_wr(.ptr(ral.module_enable), .value(prim_mubi_pkg::MuBi4False));
    // Disable intr_state
    csr_wr(.ptr(ral.intr_enable), .value(32'd0));

  endtask : body

  // Disable assertions that we expect to trigger when injecting errors
  task assert_off_err();
    cfg.entropy_src_path_vif.assert_off_err();
  endtask

endclass : entropy_src_err_vseq
