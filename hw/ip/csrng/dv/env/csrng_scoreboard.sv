// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_scoreboard extends cip_base_scoreboard #(
    .CFG_T(csrng_env_cfg),
    .RAL_T(csrng_reg_block),
    .COV_T(csrng_env_cov)
  );
  `uvm_component_utils(csrng_scoreboard)

  csrng_item                                              cs_item[];
  push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))   es_item[],
                                                          es_item_q[][$];
  uint                                                    more_cmd_data;
  bit [TL_DW-1:0]                                         hw_genbits_reg_q[$];
  bit [GENBITS_BUS_WIDTH-1:0]                             hw_genbits,
                                                          prd_genbits_q[][$];
  bit [CSRNG_BUS_WIDTH-1:0]                               cs_data[],
                                                          es_data[];
  bit                                                     fips[];

  // Sample interrupt pins at read data phase. This is used to compare with intr_state read value.
  bit [3:0] intr_pins;

  // Per-app state, sized to cfg.m_num_apps in build_phase
  bit                        genbits_fips_previous[];
  bit                        genbits_fips_received[];
  mubi4_t                    cmd_flag0_previous[];
  csrng_pkg::csrng_cmd_sts_e cmd_sts[];

  bit [3:0]            int_state_num;
  bit [MaxNumApps-1:0] int_state_read_enable;

  virtual csrng_cov_if                                    cov_vif;

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH)))   entropy_src_fifo;
  uvm_tlm_analysis_fifo#(csrng_item)   csrng_cmd_fifo[];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cs_item       = new[cfg.m_num_apps];
    es_item       = new[cfg.m_num_apps];
    es_item_q     = new[cfg.m_num_apps];
    prd_genbits_q = new[cfg.m_num_apps];
    cs_data       = new[cfg.m_num_apps];
    es_data       = new[cfg.m_num_apps];
    fips          = new[cfg.m_num_apps];
    cmd_sts       = new[cfg.m_num_apps]('{default: CMD_STS_SUCCESS});

    genbits_fips_previous = new[cfg.m_num_apps];
    genbits_fips_received = new[cfg.m_num_apps];
    cmd_flag0_previous    = new[cfg.m_num_apps];

    csrng_cmd_fifo   = new[cfg.m_num_hw_apps];
    entropy_src_fifo = new("entropy_src_fifo", this);

    for (int i = 0; i < cfg.m_num_hw_apps; i++) begin
      csrng_cmd_fifo[i] = new($sformatf("csrng_cmd_fifo[%0d]", i), this);
    end

    if (!uvm_config_db#(virtual csrng_cov_if)::get(null, "*.env" , "csrng_cov_if", cov_vif)) begin
      `uvm_fatal(`gfn, $sformatf("Failed to get csrng_cov_if from uvm_config_db"))
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      collect_seeds();
      handle_disable();
    join_none;

    for (int i = 0; i < cfg.m_num_hw_apps; i++) begin
      automatic int j = i;
      fork
        begin
          process_csrng_cmd_fifo(j);
        end
      join_none;
    end
  endtask

  virtual protected task handle_disable();
    forever begin
      wait(cfg.under_reset == 0)
      csr_spinwait(.ptr(ral.ctrl.enable),
                   .exp_data(MuBi4False),
                   .backdoor(1),
                   .timeout_ns(1_000_000_000) /* practically forever */);
      `uvm_info(`gfn, "CSRNG disabled, clearing scoreboard state.", UVM_MEDIUM)
      entropy_src_fifo.flush();
      hw_genbits = '0;
      more_cmd_data = 0;
      for (int i = 0; i < cfg.m_num_apps; i++) begin
        if (i != cfg.m_sw_app_idx) csrng_cmd_fifo[i].flush();
        es_item_q[i].delete();
        hw_genbits_reg_q.delete();
        prd_genbits_q[i].delete();
        ctr_drbg_uninstantiate(i);
        cs_data[i] = '0;
        es_data[i] = '0;
        fips[i] = '0;
        cmd_sts[i] = CMD_STS_SUCCESS;
      end
      csr_spinwait(.ptr(ral.ctrl.enable),
                   .exp_data(MuBi4True),
                   .backdoor(1),
                   .timeout_ns(1_000_000_000) /* practically forever */);
    end
  endtask

  // Wait for an item in the entropy source queue or for CSRNG getting disabled, whichever happens
  // first.  Return whether CSRNG was disabled in the `disabled` output.
  task automatic wait_es_item_or_disable(input uint app, output bit disabled);
    disabled = 0;
    `DV_SPINWAIT(
      fork
        wait(es_item_q[app].size() > 0);
        begin
          csr_spinwait(.ptr(ral.ctrl.enable),
                       .exp_data(MuBi4False),
                       .backdoor(1),
                       .timeout_ns(1_000_000_000) /* practically forever */);
          disabled = 1;
        end
      join_any
      disable fork;,
      "timeout waiting for an item in the entropy source queue or for CSRNG getting disabled",
      1_000_000_000 /* 1e9 ns = 1 s; practically forever */
    )
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    uvm_reg_data_t read_data;
    bit last_word;
    bit genbits_valid;
    uint sw_app = cfg.m_sw_app_idx;

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    csr = cfg.ral_models[ral_name].get_default_map().get_reg_by_offset(csr_addr);
    if (csr == null) begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update prediction at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        if (addr_phase_read) intr_pins = cfg.intr_vif.pins;
        if (data_phase_read && cov_vif.en_full_cov) begin
          bit [3:0] intr_en = `gmv(ral.intr_enable);
          foreach (intr_pins[i]) begin
            csrng_intr_e intr = csrng_intr_e'(i);
            `DV_CHECK_CASE_EQ(intr_pins[i], (intr_en[i] & item.d_data[i]),
                              $sformatf("Interrupt_pin: %0s", intr.name));
            if (cfg.en_cov) begin
              cov.intr_cg.sample(i, intr_en[i], item.d_data[i]);
              cov.intr_pins_cg.sample(i, intr_pins[i]);
            end
          end
        end
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        if (addr_phase_write && cov_vif.en_full_cov) begin
          bit [3:0] intr_en  = `gmv(ral.intr_enable);
          bit [3:0] intr_exp = `gmv(ral.intr_state) | item.a_data;
          foreach (intr_exp[i]) begin
            cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
          end
        end
      end
      "alert_test": begin
      end
      "regwen": begin
      end
      "ctrl": begin
      end
      "cmd_req": begin
        if (addr_phase_write) begin
          if (!more_cmd_data) begin
            cs_item[sw_app] = csrng_item::type_id::create($sformatf("cs_item[%0d]", sw_app));
            cs_item[sw_app].acmd  = acmd_e'(item.a_data[3:0]);
            cs_item[sw_app].clen  = item.a_data[7:4];
            if (item.a_data[11:8] == MuBi4True) begin
              cs_item[sw_app].flags = MuBi4True;
            end
            else begin
              cs_item[sw_app].flags = MuBi4False;
            end
            cs_item[sw_app].glen  = item.a_data[23:12];
            more_cmd_data = cs_item[sw_app].clen;
          end
          else begin
            more_cmd_data -= 1;
            cs_item[sw_app].cmd_data_q.push_back(item.a_data);
          end
          cov_vif.cg_cmds_sample(sw_app, cs_item[sw_app], cmd_flag0_previous[sw_app]);
          if (!more_cmd_data) begin
            for (int i = 0; i < cs_item[sw_app].cmd_data_q.size(); i++) begin
              cs_data[sw_app] = (cs_item[sw_app].cmd_data_q[i] << i * CmdBusWidth) +
                  cs_data[sw_app];
            end
            case (cs_item[sw_app].acmd)
              INS: begin
                // Record previous flag0 only after INS or RES commands.
                cmd_flag0_previous[sw_app] = cs_item[sw_app].flags;
                if (cs_item[sw_app].flags != MuBi4True) begin
                  // Get seed
                  bit disabled;
                  wait_es_item_or_disable(sw_app, disabled);
                  if (disabled) begin
                    `uvm_info(`gfn,
                        "Stopping to wait for entropy due to disable - Instantiate of the SW app",
                        UVM_MEDIUM)
                    return;
                  end
                  es_item[sw_app] = es_item_q[sw_app].pop_front;
                  es_data[sw_app] = es_item[sw_app].d_data[CSRNG_BUS_WIDTH-1:0];
                  fips[sw_app]    = es_item[sw_app].d_data[CSRNG_BUS_WIDTH];
                end
                ctr_drbg_instantiate(sw_app, es_data[sw_app], cs_data[sw_app], fips[sw_app]);
              end
              RES: begin
                // Record previous flag0 only after INS or RES commands.
                cmd_flag0_previous[sw_app] = cs_item[sw_app].flags;
                if (cs_item[sw_app].flags != MuBi4True) begin
                  // Get seed
                  bit disabled;
                  wait_es_item_or_disable(sw_app, disabled);
                  if (disabled) begin
                    `uvm_info(`gfn,
                        "Stopping to wait for entropy due to disable - Reseed of the SW app",
                        UVM_MEDIUM)
                    return;
                  end
                  es_item[sw_app] = es_item_q[sw_app].pop_front;
                  es_data[sw_app] = es_item[sw_app].d_data[CSRNG_BUS_WIDTH-1:0];
                  fips[sw_app]    = es_item[sw_app].d_data[CSRNG_BUS_WIDTH];
                end
                ctr_drbg_reseed(sw_app, es_data[sw_app], cs_data[sw_app], fips[sw_app]);
              end
              UPD: begin
                ctr_drbg_update(sw_app, cs_data[sw_app]);
              end
              UNI: begin
                ctr_drbg_uninstantiate(sw_app);
              end
              default: begin
                if (!GEN) begin
                  // Expect the next acknowledgement to return an error.
                  cmd_sts[sw_app] = CMD_STS_INVALID_ACMD;
                end
              end
            endcase
            cs_data[sw_app] = 'h0;
            es_data[sw_app] = 'h0;
            fips[sw_app]    = 'h0;
          end
        end
      end
      "reseed_interval": begin
      end
      "reseed_counter_0": begin
        do_read_check = 1'b0;
      end
      "reseed_counter_1": begin
        do_read_check = 1'b0;
      end
      "reseed_counter_2": begin
        do_read_check = 1'b0;
      end
      "sw_cmd_sts": begin
        do_read_check = 1'b0;
        if (data_phase_read) begin
          // If a command is being acknowledged, predict the SW command status
          // to be equal to the pre-calculated value in cmd_sts.
          if (item.d_data[2] == 1'b1) begin
            `DV_CHECK_EQ(cmd_sts[sw_app], item.d_data[5:3])
          end
        end
      end
      "genbits_vld": begin
        do_read_check = 1'b0;
        if (data_phase_read) begin
          cov_vif.cg_csrng_genbits_sample(
              .genbits_fips(item.d_data[1]),
              .genbits_fips_previous(genbits_fips_previous[sw_app]),
              .app(sw_app),
              .valid(item.d_data[0]),
              .record_transition(genbits_fips_received[sw_app] && item.d_data[0]));
          // Record the previous fips bit only if the current valid bit is high.
          if (item.d_data[0]) begin
            genbits_fips_previous[sw_app] = item.d_data[1];
            genbits_fips_received[sw_app] = 1'b1;
          end
        end
      end
      "genbits": begin
        // Only trace genbits if the genbits_vld flag is high. Since the flag is cleared
        // right when genbits are read we can not just check the value via backdoor.
        // The flag is cleared if the CSRNG is disabled or when the last word of the genbits
        // is read. After a clear the genbits_vld will still be high after the first three
        // reads. For the last read we can just check whether there is only one word left.
        csr_rd(.ptr(ral.genbits_vld), .value(read_data), .blocking(1'b1), .backdoor(1'b1));
        last_word = (hw_genbits_reg_q.size() == (GENBITS_BUS_WIDTH/TL_DW - 1));
        genbits_valid = read_data & 1'b1;
        if (genbits_valid || last_word) begin
          do_read_check = 1'b0;
          if (data_phase_read) begin
            cov_vif.cg_csrng_otp_en_sw_app_read_sample(
              .read_int_state_val_reg(1'b0),
              .read_genbits_reg(1'b1),
              .otp_en_cs_sw_app_read(cfg.otp_en_cs_sw_app_read),
              .read_int_state(ral.ctrl.read_int_state.get_mirrored_value()),
              .sw_app_enable(ral.ctrl.sw_app_enable.get_mirrored_value())
            );
            hw_genbits_reg_q.push_back(item.d_data);
            // Check if the FIPS compliance bit is set correctly.
            `DV_CHECK_EQ_FATAL((read_data >> 1) & 1'b1, cfg.compliance[sw_app])
          end
          if (hw_genbits_reg_q.size() == GENBITS_BUS_WIDTH/TL_DW) begin
            for (int i = 0; i < hw_genbits_reg_q.size(); i++) begin
              hw_genbits += hw_genbits_reg_q[i] << i*TL_DW;
            end
            cs_item[sw_app].genbits_q.push_back(hw_genbits);
            hw_genbits_reg_q.delete();
            hw_genbits = '0;
          end
          if (cs_item[sw_app].genbits_q.size() == cs_item[sw_app].glen) begin
            for (int i = 0; i < cs_item[sw_app].cmd_data_q.size(); i++) begin
              cs_data[sw_app] = (cs_item[sw_app].cmd_data_q[i] << i * CmdBusWidth) +
                  cs_data[sw_app];
            end
            ctr_drbg_generate(sw_app, cs_item[sw_app].glen, cs_data[sw_app]);
            for (int i = 0; i < cs_item[sw_app].glen; i++) begin
              `DV_CHECK_EQ_FATAL(cs_item[sw_app].genbits_q[i], prd_genbits_q[sw_app][i])
            end
            prd_genbits_q[sw_app].delete();
            cs_data[sw_app] = 'h0;
          end
        end
      end
      "int_state_read_enable": begin
      end
      "int_state_read_enable_regwen": begin
      end
      "int_state_num": begin
      end
      "int_state_val": begin
        do_read_check = 1'b0;
        if (data_phase_read) begin
          cov_vif.cg_csrng_otp_en_sw_app_read_sample(
            .read_int_state_val_reg(1'b1),
            .read_genbits_reg(1'b0),
            .otp_en_cs_sw_app_read(cfg.otp_en_cs_sw_app_read),
            .read_int_state(ral.ctrl.read_int_state.get_mirrored_value()),
            .sw_app_enable(ral.ctrl.sw_app_enable.get_mirrored_value())
          );
          csr_rd(.ptr(ral.int_state_num), .value(int_state_num), .backdoor(1'b1));
          csr_rd(.ptr(ral.int_state_read_enable), .value(int_state_read_enable), .backdoor(1'b1));
          // Unless reading of the selected internal state is enabled, the returned data must be 0.
          // If read access is indeed enabled, the actual check is performed by the
          // check_internal_state() task.
          if (`gmv(ral.ctrl.read_int_state) != MuBi4True ||
              cfg.otp_en_cs_sw_app_read != MuBi8True ||
              int_state_num >= cfg.m_num_apps ||
              int_state_read_enable[int_state_num] == 1'b0) begin
            `DV_CHECK_EQ_FATAL(item.d_data, 0)
          end
        end
      end
      "fips_force": begin
      end
      "hw_exc_sts": begin
      end
      "recov_alert_sts": begin
        if (data_phase_read && cov_vif.en_full_cov) begin
          cov_vif.cg_recov_alert_sample(item.d_data);
        end
      end
      "err_code": begin
        if (data_phase_read && cov_vif.en_full_cov) begin
          cov_vif.cg_err_code_sample(item.d_data);
        end
      end
      "err_code_test": begin
        if (data_phase_read && cov_vif.en_full_cov) begin
          cov_vif.cg_err_test_sample(item.d_data[4:0]);
        end
      end
      "main_sm_state": begin
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // TODO(#19031): post test checks - ensure that all local fifos and queues are empty
  endfunction

  // From NIST.SP.800-90Ar1
  function bit [BLOCK_LEN-1:0] block_encrypt(
      bit [KEY_LEN-1:0]   key,
      bit [BLOCK_LEN-1:0] input_block);

    bit [BLOCK_LEN-1:0]   output_block;

    sv_dpi_aes_crypt_block(.impl_i(1'b0), .op_i(1'b0), .mode_i(6'b00_0001), .key_len_i(3'b100),
                           .iv_i('h0),
                           .key_i(key),
                           .data_i(input_block),
                           .data_o(output_block));
    return output_block;
  endfunction

  function void ctr_drbg_update(uint app, bit [CSRNG_BUS_WIDTH-1:0] provided_data);

    bit [CSRNG_BUS_WIDTH-1:0]   temp;
    bit [CTR_LEN-1:0]           inc;
    bit [BLOCK_LEN-1:0]         output_block;
    bit [63:0]                  mod_val;

    `uvm_info(`gfn, $sformatf("Update of app %0d", app), UVM_MEDIUM)
    // If the instance was not instantiated then the next acknowledge should return an error.
    if (!cfg.status[app]) begin
      cmd_sts[app] = CMD_STS_INVALID_CMD_SEQ;
    end
    for (int i = 0; i < (CSRNG_BUS_WIDTH/BLOCK_LEN); i++) begin
      if (CTR_LEN < BLOCK_LEN) begin
        inc = (cfg.v[app][CTR_LEN-1:0] + 1);
        mod_val = 2**CTR_LEN;
        inc = inc % mod_val;
        cfg.v[app] = {cfg.v[app][BLOCK_LEN - 1:CTR_LEN], inc};
      end
      else begin
        cfg.v[app] += 1;
        mod_val = 2**BLOCK_LEN;
        cfg.v[app] = cfg.v[app] % mod_val;
      end

      output_block = block_encrypt(cfg.key[app], cfg.v[app]);
      temp = {temp, output_block};
    end

    temp = temp ^ provided_data;
    cfg.key[app] = temp[CSRNG_BUS_WIDTH-1:(CSRNG_BUS_WIDTH - KEY_LEN)];
    cfg.v[app] = temp[BLOCK_LEN-1:0];
  endfunction

  function void ctr_drbg_instantiate(uint app,
                                     bit [CSRNG_BUS_WIDTH-1:0] entropy_input,
                                     bit [CSRNG_BUS_WIDTH-1:0] additional_input,
                                     bit fips);

    bit [CSRNG_BUS_WIDTH-1:0] seed_material;
    bit [CSRNG_BUS_WIDTH-1:0] fips_force;
    bit compliance_previous = cfg.compliance[app];

    `uvm_info(`gfn, $sformatf("Instantiate of app %0d", app), UVM_MEDIUM)
    // If the instance was already instantiated then the next acknowledge should return an error.
    if (cfg.status[app]) begin
      cmd_sts[app] = CMD_STS_INVALID_CMD_SEQ;
    end
    seed_material  = entropy_input ^ additional_input;
    cfg.key[app] = 'h0;
    cfg.v[app]   = 'h0;
    cfg.status[app]         = 1'b1;
    ctr_drbg_update(app, seed_material);
    cfg.reseed_counter[app] = 1'b0;
    fips_force = `gmv(ral.fips_force);
    cfg.compliance[app]     = fips || ((`gmv(ral.ctrl.fips_force_enable) == MuBi4True) &&
                                       fips_force[app]);
    cov_vif.cg_csrng_state_db_sample(cfg.compliance[app], compliance_previous, app);
  endfunction

  function void ctr_drbg_reseed(uint app,
                                bit [CSRNG_BUS_WIDTH-1:0] entropy_input,
                                bit [CSRNG_BUS_WIDTH-1:0] additional_input,
                                bit fips);

    bit [CSRNG_BUS_WIDTH-1:0]   seed_material;
    bit [CSRNG_BUS_WIDTH-1:0] fips_force;
    bit compliance_previous = cfg.compliance[app];

    `uvm_info(`gfn, $sformatf("Reseed of app %0d", app), UVM_MEDIUM)
    seed_material = entropy_input ^ additional_input;
    ctr_drbg_update(app, seed_material);
    cfg.reseed_counter[app] = 1'b0;
    fips_force = `gmv(ral.fips_force);
    cfg.compliance[app]     = fips || ((`gmv(ral.ctrl.fips_force_enable) == MuBi4True) &&
                                       fips_force[app]);
    cov_vif.cg_csrng_state_db_sample(cfg.compliance[app], compliance_previous, app);
  endfunction

  function void ctr_drbg_uninstantiate(uint app);
    `uvm_info(`gfn, $sformatf("Uninstantiate of app %0d", app), UVM_MEDIUM)
    cfg.key[app] = 'h0;
    cfg.v[app]   = 'h0;
    cfg.reseed_counter[app] = 1'b0;
    cfg.compliance[app]     = 1'b0;
    cfg.status[app]         = 1'b0;
  endfunction

  function void ctr_drbg_generate(uint app,
                                  bit [11:0] glen,
                                  bit [CSRNG_BUS_WIDTH-1:0] additional_input = 'h0);

    bit [GENBITS_BUS_WIDTH-1:0]   genbits, hw_genbits;
    bit [CTR_LEN-1:0]             inc;
    bit [BLOCK_LEN-1:0]           output_block;
    bit [63:0]                    mod_val;

    `uvm_info(`gfn, $sformatf("Generate of app %0d", app), UVM_MEDIUM)
    if (cfg.reseed_counter[app] == `gmv(ral.reseed_interval)) begin
      cmd_sts[app] = CMD_STS_RESEED_CNT_EXCEEDED;
    end
    if (additional_input) begin
      ctr_drbg_update(app, additional_input);
    end
    for (int i = 0; i < glen; i++) begin
      if (CTR_LEN < BLOCK_LEN) begin
        inc = (cfg.v[app][CTR_LEN-1:0] + 1);
        mod_val = 2**CTR_LEN;
        inc = inc % mod_val;
        cfg.v[app] = {cfg.v[app][BLOCK_LEN - 1:CTR_LEN], inc};
      end
      else begin
        cfg.v[app] += 1;
        mod_val = 2**BLOCK_LEN;
        cfg.v[app] = cfg.v[app] % mod_val;
      end
      output_block = block_encrypt(cfg.key[app], cfg.v[app]);
      genbits      = output_block;
      if ((app != cfg.m_sw_app_idx) ||
          ((cfg.sw_app_enable == MuBi4True) && (cfg.otp_en_cs_sw_app_read == MuBi8True))) begin
        prd_genbits_q[app].push_back(genbits);
      end
      else begin
        prd_genbits_q[app].push_back('h0);
      end
    end
    ctr_drbg_update(app, additional_input);
    cfg.reseed_counter[app] += 1;
  endfunction

  task collect_seeds();
    push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))   es_item;
    bit [$clog2(MaxNumApps)-1:0] cmd_arb_idx;
    string      cmd_arb_idx_q_path = "tb.dut.u_csrng_core.cmd_arb_idx_q";
    bit [MaxNumApps-1:0] previous_fips;
    // Flags indicating that fips transitions can be recorded for coverage.
    bit [MaxNumApps-1:0] initial_fips_received = '0;

    `DV_CHECK_FATAL(uvm_hdl_check_path(cmd_arb_idx_q_path))
    forever begin
      entropy_src_fifo.get(es_item);
      if (cfg.lc_hw_debug_en == On) begin
        es_item.d_data = es_item.d_data ^ LC_HW_DEBUG_EN_ON_DATA;
      end
      else begin
        es_item.d_data = es_item.d_data ^ LC_HW_DEBUG_EN_OFF_DATA;
      end
      // Need to access rtl signal to determine which APP won arbitration
      `DV_CHECK(uvm_hdl_read(cmd_arb_idx_q_path, cmd_arb_idx))
      if (cmd_arb_idx < cfg.m_num_apps) begin
        es_item_q[cmd_arb_idx].push_back(es_item);
      end else begin
        `uvm_fatal(`gfn, $sformatf("Invalid entropy source arb idx: %0d", cmd_arb_idx))
      end
      cov_vif.cg_csrng_es_sample(es_item.d_data[CSRNG_BUS_WIDTH],
                                 previous_fips[cmd_arb_idx],
                                 cmd_arb_idx,
                                 initial_fips_received[cmd_arb_idx]);
      initial_fips_received[cmd_arb_idx] = 1'b1;
      previous_fips[cmd_arb_idx] = es_item.d_data[CSRNG_BUS_WIDTH];
     end
  endtask

  task process_csrng_cmd_fifo(uint app);
    forever begin
      csrng_cmd_fifo[app].get(cs_item[app]);
      cs_data[app] = '0;
      es_data[app] = '0;
      fips[app]    = 1'b0;

      // Check if the command status response is equal to the expected status.
      `DV_CHECK_EQ_FATAL(cs_item[app].status, cmd_sts[app])
      for (int i = 0; i < cs_item[app].cmd_data_q.size(); i++) begin
        cs_data[app] = (cs_item[app].cmd_data_q[i] << i * CmdBusWidth) +
                       cs_data[app];
      end
      cov_vif.cg_cmds_sample(app, cs_item[app], cmd_flag0_previous[app]);

      case (cs_item[app].acmd)
        INS: begin
          // Record previous flag0 only after INS or RES commands.
          cmd_flag0_previous[app] = cs_item[app].flags;
          if (cs_item[app].flags != MuBi4True) begin
            // Get seed
            bit disabled;
            wait_es_item_or_disable(app, disabled);
            if (disabled) begin
              `uvm_info(`gfn,
                  $sformatf("Stopping to wait for entropy due to disable - Instantiate of app %0d",
                      app),
                  UVM_MEDIUM)
              continue;
            end
            es_item[app] = es_item_q[app].pop_front();
            es_data[app] = es_item[app].d_data[CSRNG_BUS_WIDTH-1:0];
            fips[app]    = es_item[app].d_data[CSRNG_BUS_WIDTH];
          end
          ctr_drbg_instantiate(app, es_data[app], cs_data[app], fips[app]);
        end
        GEN: begin
          ctr_drbg_generate(app, cs_item[app].glen, cs_data[app]);
          for (int i = 0; i < cs_item[app].glen; i++) begin
            `DV_CHECK_EQ_FATAL(cs_item[app].genbits_q[i], prd_genbits_q[app][i])
            // Check if the FIPS compliance bit is set correctly.
            `DV_CHECK_EQ_FATAL(cs_item[app].fips_q[i], cfg.compliance[app])
            cov_vif.cg_csrng_genbits_sample(
                .genbits_fips(cs_item[app].fips_q[i]),
                .genbits_fips_previous(genbits_fips_previous[app]),
                .app(app),
                .valid(1'b1),
                .record_transition(genbits_fips_received[app]));
            genbits_fips_previous[cfg.m_sw_app_idx] = cs_item[app].fips_q[i];
            genbits_fips_received[cfg.m_sw_app_idx] = 1'b1;
          end
          // Deletes the predicted genbits before the next comparison.
          prd_genbits_q[app].delete();
        end
        UNI: begin
          ctr_drbg_uninstantiate(app);
        end
        RES: begin
          // Record previous flag0 only after INS or RES commands.
          cmd_flag0_previous[app] = cs_item[app].flags;
          if (cs_item[app].flags != MuBi4True) begin
            // Get seed
            bit disabled;
            wait_es_item_or_disable(app, disabled);
            if (disabled) begin
              `uvm_info(`gfn,
                  $sformatf("Stopping to wait for entropy due to disable - Reseed of app %0d", app),
                  UVM_MEDIUM)
              continue;
            end
            es_item[app] = es_item_q[app].pop_front();
            es_data[app] = es_item[app].d_data[CSRNG_BUS_WIDTH-1:0];
            fips[app]    = es_item[app].d_data[CSRNG_BUS_WIDTH];
          end
          ctr_drbg_reseed(app, es_data[app], cs_data[app], fips[app]);
        end
        UPD: begin
          ctr_drbg_update(app, cs_data[app]);
        end
        default: begin
          // Expect the next acknowledgement to return an error.
          cmd_sts[app] = CMD_STS_INVALID_ACMD;
        end
      endcase
    end
  endtask
endclass
