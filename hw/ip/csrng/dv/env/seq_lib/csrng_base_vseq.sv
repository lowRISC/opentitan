// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_base_vseq extends cip_base_vseq #(
    .RAL_T               (csrng_reg_block),
    .CFG_T               (csrng_env_cfg),
    .COV_T               (csrng_env_cov),
    .VIRTUAL_SEQUENCER_T (csrng_virtual_sequencer)
  );
  `uvm_object_utils(csrng_base_vseq)

  bit [csrng_env_pkg::KEY_LEN-1:0]         key;
  bit [csrng_env_pkg::BLOCK_LEN-1:0]       v;
  bit [csrng_pkg::CSRNG_CMD_WIDTH-1:0]     cmd_data_q[$];
  uint                                     reseed_counter;

  // various knobs to enable certain routines
  bit do_csrng_init = 1'b1;

  `uvm_object_new

  push_pull_device_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_entropy_src_pull_seq;
  push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)                m_edn_push_seq;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_csrng_init) csrng_init();
  endtask

  virtual task dut_shutdown();
    // check for pending csrng operations and wait for them to complete
    // TODO
  endtask

  // setup basic csrng features
  virtual task csrng_init();
    cfg.efuse_sw_app_enable_vif.drive_pin(.idx(0), .val(cfg.efuse_sw_app_enable));
  endtask

  // write csrng command request register
  virtual task wr_cmd_req(bit[3:0] acmd, bit[3:0] clen, bit[3:0] flags, bit[18:0] glen,
                          bit [31:0] data_q[$] = '{});
    csr_wr(.ptr(ral.cmd_req), .value({1'b0, glen, flags, clen, acmd}));
  endtask

  // send csrng command request
  virtual task send_cmd_req(bit[3:0] acmd, bit[3:0] clen, bit[3:0] flags, bit[18:0] glen,
                            bit[31:0] data_q[$] = '{});
    // Gen cmd_req
    cfg.m_edn_agent_cfg.m_cmd_push_agent_cfg.add_h_user_data({glen, flags, clen, acmd});
//    `DV_CHECK_FATAL(clen == data_q.size())
      m_edn_push_seq.num_trans = 1 + clen;
      for (int i = 0; i < clen; i++)
        cfg.m_edn_agent_cfg.m_cmd_push_agent_cfg.add_h_user_data(data_q.pop_front());
    // Drive cmd_req
    m_edn_push_seq.start(p_sequencer.edn_sequencer_h.m_cmd_push_sequencer);
    // Wait for cmd_ack
    cfg.m_edn_agent_cfg.vif.wait_cmd_ack();
  endtask // send_cmd_req

  // TODO: Move NIST functions to scoreboard, autochecking

  // From NIST.SP.800-90Ar1
  function bit [csrng_env_pkg::BLOCK_LEN-1:0] block_encrypt(bit [csrng_env_pkg::KEY_LEN-1:0] key,
     bit [csrng_env_pkg::BLOCK_LEN-1:0] input_block);

    if (cfg.aes_cipher_disable)
      return input_block;
    // else
  endfunction

  function void ctr_drbg_update(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] provided_data,
                                ref bit [csrng_env_pkg::KEY_LEN-1:0]       key,
                                ref bit [csrng_env_pkg::BLOCK_LEN-1:0] v);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   temp;
    bit [csrng_env_pkg::CTR_LEN-1:0]             inc;
    bit [csrng_env_pkg::BLOCK_LEN-1:0]           output_block;
    bit [63:0]                                   mod_val;

    for (int i = 0; i < (entropy_src_pkg::CSRNG_BUS_WIDTH/csrng_env_pkg::BLOCK_LEN); i++) begin
      if (csrng_env_pkg::CTR_LEN < csrng_env_pkg::BLOCK_LEN) begin
        inc = (v[csrng_env_pkg::CTR_LEN-1:0] + 1);
        mod_val = 2**csrng_env_pkg::CTR_LEN;
        inc = inc % mod_val;
        v = {v[csrng_env_pkg::BLOCK_LEN - 1:csrng_env_pkg::CTR_LEN], inc};
      end
      else begin
        v += 1;
        mod_val = 2**csrng_env_pkg::BLOCK_LEN;
        v = v % mod_val;
      end

      output_block = block_encrypt(key, v);
      temp = {temp, output_block};
    end

    temp = temp ^ provided_data;
    key  = temp[entropy_src_pkg::CSRNG_BUS_WIDTH-1:(entropy_src_pkg::CSRNG_BUS_WIDTH -
           csrng_env_pkg::KEY_LEN)];
    v    = temp[csrng_env_pkg::BLOCK_LEN-1:0];
  endfunction

  function ctr_drbg_instantiate(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input,
                                bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                                    personalization_string = 'h0);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material = entropy_input ^ personalization_string;
    key = 'h0;
    v = 'h0;
    ctr_drbg_update(seed_material, key, v);
    reseed_counter = 1;
  endfunction

  function ctr_drbg_reseed(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input,
                           bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                               additional_input = 'h0);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material = entropy_input ^ additional_input;
    ctr_drbg_update(seed_material, key, v);
    reseed_counter = 1;
  endfunction

  function csrng_update(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input);
    ctr_drbg_update(entropy_input, key, v);
  endfunction

  function bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0] ctr_drbg_generate(
           uint number_of_blocks_requested = 1,
           bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] additional_input = 'h0);

    bit [csrng_env_pkg::BLOCK_LEN-1:0]           temp;
    bit [csrng_env_pkg::CTR_LEN-1:0]             inc;
    bit [csrng_env_pkg::BLOCK_LEN-1:0]           output_block;
    bit [csrng_pkg::GENBITS_BUS_WIDTH-1:0]       returned_bits;
    bit [63:0]                                   mod_val;

    for (int i = 0; i < number_of_blocks_requested; i++) begin
      if (csrng_env_pkg::CTR_LEN < csrng_env_pkg::BLOCK_LEN) begin
        inc = (v[csrng_env_pkg::CTR_LEN-1:0] + 1);
        mod_val = 2**csrng_env_pkg::CTR_LEN;
        inc = inc % mod_val;
        v = {v[csrng_env_pkg::BLOCK_LEN - 1:csrng_env_pkg::CTR_LEN], inc};
      end
      else begin
        mod_val = 2**csrng_env_pkg::BLOCK_LEN;
        v = (v + 1) % mod_val;
      end

      output_block = block_encrypt(key, v);
      temp = output_block;
    end

    returned_bits = temp;
    ctr_drbg_update(additional_input, key, v);
    reseed_counter+=1;

    return returned_bits;
  endfunction

endclass : csrng_base_vseq
