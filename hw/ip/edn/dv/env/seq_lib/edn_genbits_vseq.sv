// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_genbits_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_genbits_vseq)
  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
      m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  uint   num_requesters, extra_requester, num_boot_reqs, num_auto_reqs,
         num_ep_reqs, num_reqs_between_reseeds, endpoint_q[$];
  uint total_glen = 0;
  state_e exp_state;
  csrng_pkg::acmd_e acmd;
  edn_env_pkg::hw_req_mode_e mode = edn_env_pkg::SwMode;

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

    // Determine boot_req_mode/auto_req_mode variables
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(extra_requester,
                                       extra_requester inside
                                       { [0:num_requesters - 1] };)

    for (int i = 0; i < num_requesters; i++) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_ep_reqs,
                                         num_ep_reqs dist
                                             { cfg.min_num_ep_reqs :/ 50,
                                               [cfg.min_num_ep_reqs:cfg.max_num_ep_reqs] :/ 50 };)
      // Add additional requests for the generated bits from auto mode or the boot sequence
      if (i == extra_requester) begin
        if (cfg.boot_req_mode == MuBi4True) begin
          num_ep_reqs += cfg.num_boot_reqs * (csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH);
        end

        if (cfg.auto_req_mode == MuBi4True) begin
          num_ep_reqs += (cfg.min_auto_reseeds + 1) * cfg.glen_auto_mode
                         * (csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH);
        end
      end
      // set total_glen to track the total number of generated words from the CSRNG
      total_glen += num_ep_reqs/(csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH);
      if (num_ep_reqs % (csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH)) begin
        total_glen += 1;
      end

      // Create/Configure endpoint_pull_seq
      m_endpoint_pull_seq[endpoint_q[i]] = push_pull_host_seq#(FIPS_ENDPOINT_BUS_WIDTH)::
          type_id::create($sformatf("m_endpoint_pull_seq[%0d]", endpoint_q[i]));
      m_endpoint_pull_seq[endpoint_q[i]].num_trans = num_ep_reqs;
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

    // set generate length and num_reqs_between_reseeds depending on the operational mode
    if (cfg.boot_req_mode == MuBi4True) begin
      mode = edn_env_pkg::BootReqMode;
      glen = total_glen - cfg.num_boot_reqs;
    end

    if (cfg.auto_req_mode == MuBi4True) begin
      mode = edn_env_pkg::AutoReqMode;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(glen, glen dist { 0 :/ 20, [1:$] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reqs_between_reseeds,
                                          num_reqs_between_reseeds inside
                                          { [1:(total_glen/cfg.glen_auto_mode)
                                               /(cfg.min_auto_reseeds + 1)] };)
      csr_wr(.ptr(ral.max_num_reqs_between_reseeds), .value(num_reqs_between_reseeds));
    end

    if ((cfg.boot_req_mode == MuBi4False) && (cfg.auto_req_mode == MuBi4False)) begin
      glen = total_glen;
    end

    if (cfg.boot_req_mode != MuBi4True) begin
      // Send instantiate cmd
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::INS), .clen(clen), .flags(flags),
             .glen(glen), .mode(mode));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type(edn_env_pkg::Sw), .cmd_data(cmd_data), .mode(mode));
      end
    end

    if (cfg.auto_req_mode != MuBi4True) begin
      // Send generate cmd
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN), .clen(clen), .flags(flags),
             .glen(glen), .mode(mode));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type(edn_env_pkg::Sw), .cmd_data(cmd_data), .mode(mode));
      end

      // Send additional sw_cmd_req cmd in sw or boot mode
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(acmd,
                                         acmd inside {csrng_pkg::UNI, csrng_pkg::RES,
                                                      csrng_pkg::UPD};)
      if (acmd == csrng_pkg::UNI) begin
        clen = 0;
      end else begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
      end
      glen = 0;

      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(acmd), .clen(clen), .flags(flags),
             .glen(glen), .mode(mode));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        wr_cmd(.cmd_type(edn_env_pkg::Sw), .cmd_data(cmd_data), .mode(mode));
      end

      // If we've sent an uninstantiate command, reinstantiate
      if (acmd == csrng_pkg::UNI) begin
        acmd = csrng_pkg::INS;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
        wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(acmd), .clen(clen), .flags(flags),
               .glen(glen), .mode(mode));
        for (int i = 0; i < clen; i++) begin
          `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
          wr_cmd(.cmd_type(edn_env_pkg::Sw), .cmd_data(cmd_data), .mode(mode));
        end
      end
    end

    if (cfg.auto_req_mode == MuBi4True) begin
      // Get random auto mode state
      if (num_reqs_between_reseeds) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                           exp_state inside {AutoDispatch, AutoCaptGenCnt,
                                                             AutoSendGenCmd, AutoCaptReseedCnt,
                                                             AutoSendReseedCmd, AutoAckWait};)
      // If num_reqs_between_reseeds is 0 we will never enter the auto generate states
      end else begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                           exp_state inside {AutoDispatch, AutoCaptReseedCnt,
                                                             AutoSendReseedCmd, AutoAckWait};)
      end

      // write a random sw command to the sw_cmd_req register
      // this command should not be allowed to appear at the CSRNG cmd interface
      `uvm_info(`gfn, $sformatf("Waiting for main_sm to reach state %s",
                                exp_state.name()), UVM_HIGH)
      csr_spinwait(.ptr(ral.main_sm_state), .exp_data(exp_state), .backdoor(1'b1));
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(glen, glen dist { 0 :/ 20, [1:$] :/ 80 };)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(acmd,
                                         acmd inside {csrng_pkg::INS, csrng_pkg::GEN,
                                                      csrng_pkg::RES, csrng_pkg::UPD,
                                                      csrng_pkg::UNI};)
      cov_vif.cg_cs_cmds_sample(.acmd(acmd), .clen(clen), .flags(flags),
                                .glen(glen), .mode(mode), .cmd_src(edn_env_pkg::Sw));
      csr_wr(.ptr(ral.sw_cmd_req), .value({glen, flags, clen, 1'b0, acmd}));
      for (int i = 0; i < clen; i++) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
        csr_wr(.ptr(ral.sw_cmd_req), .value(cmd_data));
      end
      // Disable auto_req_mode after the minimum number of expected reseeds
      wait (cfg.m_csrng_agent_cfg.reseed_cnt >= cfg.min_auto_reseeds)
      ral.ctrl.auto_req_mode.set(MuBi4False);
      csr_update(.csr(ral.ctrl));
      mode = edn_env_pkg::SwMode;
      // Give the hardware time to quiesce
      csr_spinwait(.ptr(ral.main_sm_state), .exp_data(edn_pkg::Idle), .backdoor(1'b1));
      `DV_CHECK_EQ(cfg.m_csrng_agent_cfg.generate_between_reseeds_cnt, num_reqs_between_reseeds)
      // If the endpoint agents still expect more data, send another generate command
      if (total_glen > cfg.m_csrng_agent_cfg.generate_cnt*cfg.glen_auto_mode) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(clen, clen dist { 0 :/ 20, [1:12] :/ 80 };)
        `DV_CHECK_STD_RANDOMIZE_FATAL(flags)
        glen = total_glen - cfg.m_csrng_agent_cfg.generate_cnt*cfg.glen_auto_mode;
        wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::GEN), .clen(clen), .flags(flags),
               .glen(glen), .mode(mode));
        for (int i = 0; i < clen; i++) begin
          `DV_CHECK_STD_RANDOMIZE_FATAL(cmd_data)
          wr_cmd(.cmd_type(edn_env_pkg::Sw), .cmd_data(cmd_data), .mode(mode));
        end
      end
    end

    // uninstantiate CSRNG instance
    mode = edn_env_pkg::SwMode;
    wr_cmd(.cmd_type(edn_env_pkg::Sw), .acmd(csrng_pkg::UNI), .mode(mode));

  endtask

endclass
