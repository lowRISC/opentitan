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
  csrng_item              cs_item;
  bit [TL_DW-1:0]         rdata;
  bit [RSD_CTR_LEN-1:0]   reseed_counter;
  bit [BLOCK_LEN-1:0]     v;
  bit [KEY_LEN-1:0]       key;


  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)))
      entropy_src_fifo;
  uvm_tlm_analysis_fifo#(csrng_item)   csrng_cmd_fifo;

  // local queues to hold incoming packets pending comparison
  push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
      entropy_src_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    entropy_src_fifo = new("entropy_src_fifo", this);
    csrng_cmd_fifo   = new("csrng_cmd_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      process_entropy_src_fifo();
      process_csrng_cmd_fifo();
    join_none
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
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
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

    // Compare internal state
  task check_int_state();
// TODO: Halt main state machine and poll first
// TODO: Check FIPs and instantiated too
    csr_wr(.ptr(ral.int_state_num), .value(1'b0));
    for (int i = 0; i < RSD_CTR_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      reseed_counter = (rdata<<TL_DW*i) + reseed_counter;
    end
    `DV_CHECK_EQ_FATAL(reseed_counter, cfg.reseed_counter)
    for (int i = 0; i < BLOCK_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      v = (rdata<<TL_DW*i) + v;
    end
    `DV_CHECK_EQ_FATAL(v, cfg.v)
    for (int i = 0; i < KEY_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      key = (rdata<<TL_DW*i) + key;
    end
    `DV_CHECK_EQ_FATAL(key, cfg.key)
  endtask

  // From NIST.SP.800-90Ar1
  function bit [csrng_env_pkg::BLOCK_LEN-1:0] block_encrypt(bit [csrng_env_pkg::KEY_LEN-1:0] key,
      bit [csrng_env_pkg::BLOCK_LEN-1:0] input_block);

    bit [csrng_env_pkg::BLOCK_LEN-1:0]   output_block;

    if (cfg.aes_cipher_disable)
      output_block = input_block;
    else begin
      sv_dpi_aes_crypt_block(.impl_i(1'b0), .op_i(1'b0), .mode_i(6'b00_0001), .key_len_i(3'b100),
                             .iv_i('h0),
                             .key_i(key),
                             .data_i(input_block),
                             .data_o(output_block));
    end
    return output_block;
  endfunction

  function void ctr_drbg_update(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] provided_data,
                                ref bit [csrng_env_pkg::KEY_LEN-1:0]       key,
                                ref bit [csrng_env_pkg::BLOCK_LEN-1:0]     v);

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

  function void ctr_drbg_instantiate(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input,
                                     bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                                         personalization_string = 'h0);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material = entropy_input ^ personalization_string;
    cfg.key = 'h0;
    cfg.v = 'h0;
    ctr_drbg_update(seed_material, cfg.key, cfg.v);
    cfg.reseed_counter = 1'b1;
  endfunction

  function void ctr_drbg_reseed(bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0] entropy_input,
                                bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]
                                    additional_input = 'h0);

    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed_material;

    seed_material = entropy_input ^ additional_input;
    ctr_drbg_update(seed_material, cfg.key, cfg.v);
    cfg.reseed_counter = 1'b1;
  endfunction

  virtual task process_csrng_cmd_fifo();
    bit [entropy_src_pkg::CSRNG_BUS_WIDTH-1:0]   seed;

    forever begin
      csrng_cmd_fifo.get(cs_item);
      for (int i = 0; i < cs_item.cmd_data_q.size(); i++) begin
        seed = (cs_item.cmd_data_q[i] << i * 32) + seed;
      end

      case (cs_item.acmd)
        csrng_pkg::INS: begin
          ctr_drbg_instantiate(seed);
        end
      endcase

      check_int_state();
    end
  endtask

endclass
