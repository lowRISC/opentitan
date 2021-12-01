// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_base_vseq extends cip_base_vseq #(
    .RAL_T               (entropy_src_reg_block),
    .CFG_T               (entropy_src_env_cfg),
    .COV_T               (entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T (entropy_src_virtual_sequencer)
  );
  `uvm_object_utils(entropy_src_base_vseq)

  rand bit [3:0]   rng_val;

  // The actual number of seeds that should be expected out
  // of the current sequence (given predicted health check failures)
  uint        seed_cnt_actual;

  push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)          m_rng_push_seq;
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_csrng_pull_seq;

  // various knobs to enable certain routines
  bit  do_entropy_src_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_entropy_src_init) entropy_src_init();
  endtask

  virtual task dut_shutdown();
    // check for pending entropy_src operations and wait for them to complete
    // TODO
  endtask

  // setup basic entropy_src features
  virtual task entropy_src_init();
    // Fuses
    cfg.otp_en_es_fw_read_vif.drive(.val(cfg.otp_en_es_fw_read));
    cfg.otp_en_es_fw_over_vif.drive(.val(cfg.otp_en_es_fw_over));

    // Register write enable
    // TODO Do we need to check main_sm_idle before writing DUT registers?
    csr_wr(.ptr(ral.regwen), .value(cfg.regwen));

    // Controls
    ral.entropy_control.es_type.set(cfg.type_bypass);
    ral.entropy_control.es_route.set(cfg.route_software);
    csr_update(.csr(ral.entropy_control));

    // Enables
    ral.conf.enable.set(cfg.enable);
    ral.conf.entropy_data_reg_enable.set(cfg.entropy_data_reg_enable);
    ral.conf.boot_bypass_disable.set(cfg.boot_bypass_disable);
    ral.conf.rng_bit_enable.set(cfg.rng_bit_enable);
    ral.conf.rng_bit_sel.set(cfg.rng_bit_sel);
    csr_update(.csr(ral.conf));

  endtask

  virtual function queue_of_rng_val_t generate_rng_data(int quad_cnt);
    queue_of_rng_val_t result;

    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")

    return result;
  endfunction

  // return zero if this next set of rng values would cause a health check failure,
  // based on the currently configured thresholds.
  virtual function bit health_check_rng_data(queue_of_rng_val_t sample);
    // TODO: Implement this
    return 0;
  endfunction

  // Load enough data into the rng_push_seq to create the next seed.
  //
  // This function needs to take into account the current configuation
  // (is SHA3 always bypassed? Is boot bypass disabled?) as well as
  // the fact that some data may be discarded due to health check failures.

  // In the case of anticipated health check failures, the failing
  // data is loaded anyway, but more data is created to extend the sequence.
  //
  // Returns 1 on failure, 0 otherwise.
  virtual function bit load_rng_push_seq_single_seed(int seed_idx);

    int window_size;
    entropy_phase_e phase;
    int retry_limit, retry_cnt;
    bit status;
    queue_of_rng_val_t window_sample;

    phase = convert_seed_idx_to_phase(seed_idx,
                                      cfg.boot_bypass_disable == prim_mubi_pkg::MuBi4True);
    window_size = rng_window_size(seed_idx,
                                  cfg.type_bypass == prim_mubi_pkg::MuBi4True,
                                  cfg.boot_bypass_disable == prim_mubi_pkg::MuBi4True,
                                  cfg.fips_window_size);

    retry_limit = (phase == BOOT) ? cfg.boot_mode_retry_limit :
                  (phase == STARTUP) ? 2 :
                  0; // CONTINUOUS PHASE: No retries necessary.
                     // Occasional failing data is passed on.
    retry_cnt   = 0;

    do begin
      // TODO: properly handle rng bit-select config
      window_sample = generate_rng_data(window_size / 4);
      status = health_check_rng_data(window_sample);
      retry_cnt++;
      if(retry_limit && retry_cnt >= retry_limit) break;
    end while(status);

    if(status) begin
      return status;
    end

    do begin
      m_rng_push_seq.num_trans++;
      cfg.m_rng_agent_cfg.add_h_user_data(window_sample.pop_front());
    end while(window_sample.size() > 0);

    return status;

  endfunction : load_rng_push_seq_single_seed

  virtual function int load_rng_push_seq();
    int seed_cnt = 0;

    m_rng_push_seq.num_trans = 0;
    for (int i = 0; i < cfg.seed_cnt; i++) begin
      seed_cnt += (load_rng_push_seq_single_seed(i) == 0);
    end

    return seed_cnt;
  endfunction

  virtual task init_rng_push_seq();
    // Create and start rng host sequence
    m_rng_push_seq = push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)::type_id::
        create("m_rng_push_seq");
    seed_cnt_actual = load_rng_push_seq();
    m_rng_push_seq.start(p_sequencer.rng_sequencer_h);
  endtask

endclass : entropy_src_base_vseq
