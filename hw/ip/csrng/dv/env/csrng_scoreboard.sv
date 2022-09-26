// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_scoreboard extends cip_base_scoreboard #(
    .CFG_T(csrng_env_cfg),
    .RAL_T(csrng_reg_block),
    .COV_T(csrng_env_cov)
  );
  `uvm_component_utils(csrng_scoreboard)

  csrng_item                                              cs_item[NUM_HW_APPS + 1];
  push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))   es_item[NUM_HW_APPS + 1],
                                                          es_item_q[NUM_HW_APPS + 1][$];
  uint                                                    more_cmd_data;
  bit [TL_DW-1:0]                                         hw_genbits_reg_q[$];
  bit [GENBITS_BUS_WIDTH-1:0]                             hw_genbits,
                                                          prd_genbits_q[NUM_HW_APPS + 1][$];
  bit [CSRNG_BUS_WIDTH-1:0]                               cs_data[NUM_HW_APPS + 1],
                                                          es_data[NUM_HW_APPS + 1];
  bit                                                     fips[NUM_HW_APPS + 1];

  virtual csrng_cov_if                                    cov_vif;

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH)))   entropy_src_fifo;
  uvm_tlm_analysis_fifo#(csrng_item)   csrng_cmd_fifo[NUM_HW_APPS];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    entropy_src_fifo = new("entropy_src_fifo", this);

    for (int i = 0; i < NUM_HW_APPS; i++) begin
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
    join_none;

    for (int i = 0; i < NUM_HW_APPS; i++) begin
      automatic int j = i;
      fork
        begin
          process_csrng_cmd_fifo(j);
        end
      join_none;
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "regwen": begin
      end
      "ctrl": begin
      end
      "sum_sts": begin
      end
      "cmd_req": begin
        if (addr_phase_write) begin
          if (!more_cmd_data) begin
            cs_item[SW_APP] = csrng_item::type_id::create("cs_item[SW_APP]");
            cs_item[SW_APP].acmd  = acmd_e'(item.a_data[3:0]);
            cs_item[SW_APP].clen  = item.a_data[7:4];
            if (item.a_data[11:8] == MuBi4True) begin
              cs_item[SW_APP].flags = MuBi4True;
            end
            else begin
              cs_item[SW_APP].flags = MuBi4False;
            end
            cs_item[SW_APP].glen  = item.a_data[30:12];

            more_cmd_data = cs_item[SW_APP].clen;
          end
          else begin
            more_cmd_data -= 1;
            cs_item[SW_APP].cmd_data_q.push_back(item.a_data);
          end
          cov_vif.cg_cmds_sample(SW_APP, cs_item[SW_APP]);
          if (!more_cmd_data) begin
            for (int i = 0; i < cs_item[SW_APP].cmd_data_q.size(); i++) begin
              cs_data[SW_APP] = (cs_item[SW_APP].cmd_data_q[i] << i * CSRNG_CMD_WIDTH) +
                  cs_data[SW_APP];
            end
            case (cs_item[SW_APP].acmd)
              INS: begin
                if (cs_item[SW_APP].flags != MuBi4True) begin
                  // Get seed
                  wait (es_item_q[SW_APP].size());
                  es_item[SW_APP] = es_item_q[SW_APP].pop_front;
                  es_data[SW_APP] = es_item[SW_APP].d_data[CSRNG_BUS_WIDTH-1:0];
                  fips[SW_APP]    = es_item[SW_APP].d_data[CSRNG_BUS_WIDTH];
                end
                ctr_drbg_instantiate(SW_APP, es_data[SW_APP], cs_data[SW_APP], fips[SW_APP]);
              end
              RES: begin
                if (cs_item[SW_APP].flags != MuBi4True) begin
                  // Get seed
                  wait (es_item_q[SW_APP].size());
                  es_item[SW_APP] = es_item_q[SW_APP].pop_front;
                  es_data[SW_APP] = es_item[SW_APP].d_data[CSRNG_BUS_WIDTH-1:0];
                  fips[SW_APP]    = es_item[SW_APP].d_data[CSRNG_BUS_WIDTH];
                end
                ctr_drbg_reseed(SW_APP, es_data[SW_APP], cs_data[SW_APP], fips[SW_APP]);
              end
              UPD: begin
                ctr_drbg_update(SW_APP, cs_data[SW_APP]);
              end
              UNI: begin
                ctr_drbg_uninstantiate(SW_APP);
              end
              default: begin
                if (!GEN) begin
                  `uvm_fatal(`gfn, $sformatf("Invalid csrng.acmd: 0x%0h", cs_item[SW_APP].acmd))
                end
              end
            endcase
            cs_data[SW_APP] = 'h0;
            es_data[SW_APP] = 'h0;
            fips[SW_APP]    = 'h0;
          end
        end
      end
      "sw_cmd_sts": begin
        do_read_check = 1'b0;
      end
      "genbits_vld": begin
        do_read_check = 1'b0;
      end
      "genbits": begin
        do_read_check = 1'b0;
        if (data_phase_read) begin
          hw_genbits_reg_q.push_back(item.d_data);
        end
        if (hw_genbits_reg_q.size() == GENBITS_BUS_WIDTH/TL_DW) begin
          for (int i = 0; i < hw_genbits_reg_q.size(); i++) begin
            hw_genbits += hw_genbits_reg_q[i] << i*TL_DW;
          end
          cs_item[SW_APP].genbits_q.push_back(hw_genbits);
          hw_genbits_reg_q.delete();
          hw_genbits = '0;
        end
        if (cs_item[SW_APP].genbits_q.size() == cs_item[SW_APP].glen) begin
          for (int i = 0; i < cs_item[SW_APP].cmd_data_q.size(); i++) begin
            cs_data[SW_APP] = (cs_item[SW_APP].cmd_data_q[i] << i * CSRNG_CMD_WIDTH) +
                cs_data[SW_APP];
          end
          ctr_drbg_generate(SW_APP, cs_item[SW_APP].glen, cs_data[SW_APP]);
          for (int i = 0; i < cs_item[SW_APP].glen; i++) begin
            `DV_CHECK_EQ_FATAL(cs_item[SW_APP].genbits_q[i], prd_genbits_q[SW_APP][i])
          end
          prd_genbits_q[SW_APP].delete();
          cs_data[SW_APP] = 'h0;
        end
      end
      "halt_main_sm": begin
      end
      "main_sm_sts": begin
        do_read_check = 1'b0;
      end
      "int_state_val": begin
        do_read_check = 1'b0;
      end
      "int_state_num": begin
      end
      "hw_exc_sts": begin
      end
      "err_code": begin
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
    // post test checks - ensure that all local fifos and queues are empty
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

    bit [CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material  = entropy_input ^ additional_input;
    cfg.key[app] = 'h0;
    cfg.v[app]   = 'h0;
    ctr_drbg_update(app, seed_material);
    cfg.reseed_counter[app] = 1'b1;
    cfg.compliance[app]     = fips;
    cfg.status[app]         = 1'b1;
  endfunction

  function void ctr_drbg_reseed(uint app,
                                bit [CSRNG_BUS_WIDTH-1:0] entropy_input,
                                bit [CSRNG_BUS_WIDTH-1:0] additional_input,
                                bit fips);

    bit [CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material = entropy_input ^ additional_input;
    ctr_drbg_update(app, seed_material);
    cfg.reseed_counter[app] = 1'b1;
    cfg.compliance[app]     = fips;
  endfunction

  function void ctr_drbg_uninstantiate(uint app);
    cfg.key[app] = 'h0;
    cfg.v[app]   = 'h0;
    cfg.reseed_counter[app] = 1'b0;
    cfg.compliance[app]     = 1'b0;
    cfg.status[app]         = 1'b0;
  endfunction

  function void ctr_drbg_generate(uint app,
                                  bit [18:0] glen,
                                  bit [CSRNG_BUS_WIDTH-1:0] additional_input = 'h0);

    uint                          requested_bits;
    bit [GENBITS_BUS_WIDTH-1:0]   genbits, hw_genbits;
    bit [CTR_LEN-1:0]             inc;
    bit [BLOCK_LEN-1:0]           output_block;
    bit [63:0]                    mod_val;

    if (additional_input) begin
      ctr_drbg_update(app, additional_input);
    end
    requested_bits = glen * GENBITS_BUS_WIDTH;
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
      if ((app != SW_APP) ||
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
    bit [1:0]   cmd_arb_idx;
    string      cmd_arb_idx_q_path = "tb.dut.u_csrng_core.cmd_arb_idx_q";

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
      case (cmd_arb_idx)
        HW_APP0: begin
                   es_item_q[HW_APP0].push_back(es_item);
                 end
        HW_APP1: begin
                   es_item_q[HW_APP1].push_back(es_item);
                 end
        SW_APP:  begin
                   es_item_q[SW_APP].push_back(es_item);
                 end
        default: begin
          `uvm_fatal(`gfn, $sformatf("Invalid APP: %0d", cmd_arb_idx))
        end
      endcase
     end
  endtask

  task process_csrng_cmd_fifo(bit[NUM_HW_APPS-1:0] app);
    forever begin
      csrng_cmd_fifo[app].get(cs_item[app]);
      cs_data[app] = '0;
      es_data[app] = '0;
      fips[app]    = 1'b0;
      for (int i = 0; i < cs_item[app].cmd_data_q.size(); i++) begin
        cs_data[app] = (cs_item[app].cmd_data_q[i] << i * CSRNG_CMD_WIDTH) +
                       cs_data[app];
      end
      cov_vif.cg_cmds_sample(app, cs_item[app]);

      case (cs_item[app].acmd)
        INS: begin
          if (cs_item[app].flags != MuBi4True) begin
            // Get seed
            wait (es_item_q[app].size());
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
          end
        end
        UNI: begin
          ctr_drbg_uninstantiate(app);
        end
        RES: begin
          if (cs_item[app].flags != MuBi4True) begin
            // Get seed
            wait (es_item_q[app].size());
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
          `uvm_fatal(`gfn, $sformatf("Invalid csrng_acmd: 0x%0h", cs_item[app].acmd))
        end
      endcase
    end
  endtask
endclass
