// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_scoreboard extends cip_base_scoreboard #(
    .CFG_T(csrng_env_cfg),
    .RAL_T(csrng_reg_block),
    .COV_T(csrng_env_cov)
  );
  `uvm_component_utils(csrng_scoreboard)

  // local variables
  bit [RSD_CTR_LEN-1:0]   reseed_counter;
  bit [BLOCK_LEN-1:0]     v;
  bit [KEY_LEN-1:0]       key;


  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)))
      entropy_src_fifo;
  uvm_tlm_analysis_fifo#(csrng_item)   csrng_cmd_fifo[NUM_HW_APPS];

  // local queues to hold incoming packets pending comparison
  push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
      entropy_src_q[$];
  bit [csrng_pkg::GENBITS_BUS_WIDTH-1 : 0]    genbits_q[NUM_HW_APPS][$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    entropy_src_fifo = new("entropy_src_fifo", this);
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      csrng_cmd_fifo[i] = new($sformatf("csrng_cmd_fifo[%0d]", i), this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      process_entropy_src_fifo();

      for (int i = 0; i < NUM_HW_APPS; i++) begin
        automatic int j = i;
        fork
          begin
            process_csrng_cmd_fifo(j);
          end
        join_none;
      end
    join
  endtask

  virtual task process_entropy_src_fifo();
    push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))  item;
    forever begin
      entropy_src_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received entropy_src item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
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
      end
      "sw_cmd_sts": begin
        do_read_check = 1'b0;
      end
      "genbits_vld": begin
        do_read_check = 1'b0;
      end
      "genbits": begin
        do_read_check = 1'b0;
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

  function void capture_genbits(bit [NUM_HW_APPS-1:0] hwapp,
                                bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0] genbits);
    genbits_q[hwapp].push_back(genbits);
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

  function void ctr_drbg_update(uint hwapp,
                                bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] provided_data);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   temp;
    bit [CTR_LEN-1:0]                            inc;
    bit [BLOCK_LEN-1:0]                          output_block;
    bit [63:0]                                   mod_val;

    for (int i = 0; i < (entropy_src_pkg::CSRNG_BUS_WIDTH/BLOCK_LEN); i++) begin
      if (CTR_LEN < BLOCK_LEN) begin
        inc = (cfg.v[hwapp][CTR_LEN-1:0] + 1);
        mod_val = 2**CTR_LEN;
        inc = inc % mod_val;
        cfg.v[hwapp] = {cfg.v[hwapp][BLOCK_LEN - 1:CTR_LEN], inc};
      end
      else begin
        cfg.v[hwapp] += 1;
        mod_val = 2**BLOCK_LEN;
        cfg.v[hwapp] = cfg.v[hwapp] % mod_val;
      end

      output_block = block_encrypt(cfg.key[hwapp], cfg.v[hwapp]);
      temp = {temp, output_block};
    end

    temp = temp ^ provided_data;
    cfg.key[hwapp] = temp[entropy_src_pkg::CSRNG_BUS_WIDTH-1:(entropy_src_pkg::CSRNG_BUS_WIDTH -
        KEY_LEN)];
    cfg.v[hwapp] = temp[BLOCK_LEN-1:0];
  endfunction

  function void ctr_drbg_instantiate(uint hwapp,
                                     bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input,
                                     bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                                         personalization_string = 'h0);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material  = entropy_input ^ personalization_string;
    cfg.key[hwapp] = 'h0;
    cfg.v[hwapp]   = 'h0;
    ctr_drbg_update(hwapp, seed_material);
    cfg.reseed_counter[hwapp] = 1'b1;
    cfg.status[hwapp]         = 1'b1;
  endfunction

  function void ctr_drbg_reseed(uint hwapp,
                                bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input,
                                bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                                    additional_input = 'h0);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material = entropy_input ^ additional_input;
    ctr_drbg_update(hwapp, seed_material);
    cfg.reseed_counter[hwapp] = 1'b1;
  endfunction

  function void ctr_drbg_uninstantiate(uint hwapp);
    cfg.key[hwapp] = 'h0;
    cfg.v[hwapp]   = 'h0;
    cfg.reseed_counter[hwapp] = 1'b0;
    cfg.status[hwapp]         = 1'b0;
  endfunction

  function void ctr_drbg_generate(uint hwapp,
                                  bit [18:0] requested_genbits,
                                  bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                                      additional_input = 'h0);

    uint                                     requested_bits;
    bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0]   genbits;
    bit [CTR_LEN-1:0]                        inc;
    bit [BLOCK_LEN-1:0]                      output_block;
    bit [63:0]                               mod_val;

    requested_bits = requested_genbits * csrng_pkg::GENBITS_BUS_WIDTH;
    for (int i = 0; i < requested_genbits; i++) begin
      if (CTR_LEN < BLOCK_LEN) begin
        inc = (cfg.v[hwapp][CTR_LEN-1:0] + 1);
        mod_val = 2**CTR_LEN;
        inc = inc % mod_val;
        cfg.v[hwapp] = {cfg.v[hwapp][BLOCK_LEN - 1:CTR_LEN], inc};
      end
      else begin
        cfg.v[hwapp] += 1;
        mod_val = 2**BLOCK_LEN;
        cfg.v[hwapp] = cfg.v[hwapp] % mod_val;
      end
      output_block = block_encrypt(cfg.key[hwapp], cfg.v[hwapp]);
      genbits      = output_block;
      `uvm_info(`gfn, $sformatf("genbits[%0d]      = %h", hwapp, genbits), UVM_DEBUG)
      `uvm_info(`gfn, $sformatf("genbits_q[%0d][0] = %h", hwapp, genbits_q[hwapp][0]), UVM_DEBUG)
      `DV_CHECK_EQ_FATAL(genbits, genbits_q[hwapp].pop_front())
    end
    ctr_drbg_update(hwapp, additional_input);
    cfg.reseed_counter[hwapp] += 1;
  endfunction

  task process_csrng_cmd_fifo(uint hwapp);
    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed;
    csrng_item                                   cs_item;

    forever begin
        csrng_cmd_fifo[hwapp].get(cs_item);
        `uvm_info(`gfn, $sformatf("received csrng_cmd:\n%0s", cs_item.convert2string()), UVM_HIGH)
        seed = '0;
        for (int i = 0; i < cs_item.cmd_data_q.size(); i++) begin
          seed = (cs_item.cmd_data_q[i] << i * csrng_pkg::CSRNG_CMD_WIDTH) + seed;
        end

        case (cs_item.acmd)
          csrng_pkg::INS: begin
            @(posedge cfg.m_edn_agent_cfg[hwapp].vif.mon_cb.cmd_rsp.csrng_rsp_ack);
            ctr_drbg_instantiate(hwapp, seed);
          end
          csrng_pkg::GEN: begin
            for (int i = 0; i < cs_item.glen; i++) begin
              @(posedge cfg.m_edn_agent_cfg[hwapp].vif.mon_cb.cmd_rsp.genbits_valid);
              capture_genbits(hwapp, cfg.m_edn_agent_cfg[hwapp].vif.mon_cb.cmd_rsp.genbits_bus);
            end
            @(posedge cfg.m_edn_agent_cfg[hwapp].vif.mon_cb.cmd_rsp.csrng_rsp_ack);
            ctr_drbg_generate(hwapp, cs_item.glen);
          end
          csrng_pkg::UNI: begin
            @(posedge cfg.m_edn_agent_cfg[hwapp].vif.mon_cb.cmd_rsp.csrng_rsp_ack);
            ctr_drbg_uninstantiate(hwapp);
          end
        endcase
      end
  endtask

endclass
