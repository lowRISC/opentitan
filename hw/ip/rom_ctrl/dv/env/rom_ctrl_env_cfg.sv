// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rom_ctrl_regs_reg_block));

  `uvm_object_utils(rom_ctrl_env_cfg)

  // ext component cfgs
  rand kmac_app_agent_cfg m_kmac_agent_cfg;

  // The upper bound to use for response delays in the KMAC app agent
  //
  // This is randomised with rom_ctrl_env_cfg, then copied to m_kmac_agent_cfg in post_randomize().
  // (Doing so works because nothing in the randomisation of m_kmac_agent_cfg depends on its
  // rsp_delay_max).
  rand int unsigned m_kmac_rsp_delay_max;

  // Memory backdoor util instance for ROM.
  rom_ctrl_bkdr_util rom_ctrl_bkdr_util_h;

  // ext interfaces
  rom_ctrl_vif rom_ctrl_vif;

  // For block-level testing, there's a parameterized reg_block class that was added manually to
  // allow the testbench infrastructure to support memories with configurable size. Top-level
  // testing is much easier: there, the top-level has configured the size of the memory for us.
  //
  // These are the names of the RAL to use for block-level and chip-level tests, respectively.
  local string m_block_level_rom_ral_name = "rom_ctrl_prim_reg_block";
  local string m_chip_level_rom_ral_name  = "rom_ctrl_rom_reg_block";

  // The key that is used for scrambling the ROM. If not configured, this will be RND_CNST_SCR_KEY
  // (a global parameter), but this is unlikely to match the design under test.
  bit [127:0] m_scramble_key = RND_CNST_SCR_KEY;

  // The nonce that is used for scrambling the ROM. If not configured, this will be
  // RND_CNST_SCR_NONCE (a global parameter), but this is unlikely to match the design under test.
  bit [63:0]  m_scramble_nonce = RND_CNST_SCR_NONCE;

  // An interface bound into the rom_ctrl_compare module
  virtual rom_ctrl_compare_if compare_vif;

  // An interface bound into the rom_ctrl_fsm module
  virtual rom_ctrl_fsm_if fsm_vif;

  // A handle to the scoreboard, used to flag expected errors.
  rom_ctrl_scoreboard scoreboard;

  // A flag that tells the environment to use rom_ctrl_fsm_if to force the value of the ROM address
  // counter, skipping over the middle of ROM.
  //
  // This is set in the rom_ctrl_env_cfg constructor (based on the +skip_middle plusarg) and can be
  // accessed with get_skip_middle().
  local bit m_skip_middle;

  extern function new (string name="");
  extern function void post_randomize();

  extern virtual function void initialize(bit inherit_ral_models = 1'b0);
  extern virtual protected function dv_base_reg_block create_ral_by_name(string name);

  // Retrieve the flag that says whether we should skip reading the middle of ROM. If true, this was
  // set with the +skip_middle plusarg.
  extern function bit get_skip_middle();

  // Return true if ral_name is the name of the RAL for the ROM itself
  extern function bit is_rom_ral_name(string ral_name);

  // Return a uvm_mem representing the ROM itself (from either the RAL called
  // m_block_level_rom_ral_name or the one called m_chip_level_rom_ral_name).
  extern function uvm_mem get_rom_ral();

  // Return the size of ROM in bytes
  extern function int unsigned get_rom_size_bytes();

  // Read the expected digest from the top DIGEST_SIZE bits of ROM (through a backdoor)
  extern function bit [DIGEST_SIZE-1:0] get_expected_digest();

  // Control the device-side delay for the kmac app agent that talks to the dut. If it is large,
  // rom_ctrl will spend all its time waiting for kmac to accept words that rom_ctrl is trying to
  // send to kmac. Randomise this to be small with high probability and occasionally make it 10 (to
  // check that the interface from rom_ctrl to kmac can be stalled properly).
  extern constraint rsp_delay_max_c;
endclass

function rom_ctrl_env_cfg::new (string name="");
  super.new(name);

  can_reset_with_csr_accesses = 1'b1;

  list_of_alerts = rom_ctrl_env_pkg::LIST_OF_ALERTS;
  tl_intg_alert_name = "fatal";

  num_interrupts = 0;

  m_kmac_agent_cfg = kmac_app_agent_cfg::type_id::create("m_kmac_agent_cfg");
  m_kmac_agent_cfg.if_mode = dv_utils_pkg::Device;
  m_kmac_agent_cfg.constant_share_means_error = 1'b0;
  // The checker reads the upper 8 words of ROM which takes 9 cycles. The rsp_delay_max has been
  // rounded off by 9*2=18 cycles along with adding 2 just to give an extra precision.
  m_kmac_agent_cfg.rsp_delay_min = 'd0;
  m_kmac_agent_cfg.rsp_delay_max = 'd20;

  sec_cm_alert_name = "fatal";

  if ($value$plusargs("skip_middle_of_rom=%0b", m_skip_middle)) begin
    `uvm_info("skip_middle_mode",
              $sformatf("Setting m_skip_middle to %d, based on plusarg.", m_skip_middle),
              UVM_HIGH)
  end else begin
    `uvm_info("skip_middle_mode",
              $sformatf("Leaving m_skip_middle=%d (no +skip_middle_of_rom plusarg).",
                        m_skip_middle),
              UVM_HIGH)
  end
endfunction

function void rom_ctrl_env_cfg::post_randomize();
  super.post_randomize();
  m_kmac_agent_cfg.rsp_delay_max = m_kmac_rsp_delay_max;
endfunction

function void rom_ctrl_env_cfg::initialize(bit inherit_ral_models = 1'b0);
  // Infer the name where the ROM interface will be defined from the inherit_ral_models argument. If
  // it is false, this is a block-level test and we should use "rom_ctrl_prim_reg_block" (the
  // manually defined block in the environment). If it is true, this is a chip-level test and it
  // should already have an instance of "rom_ctrl_rom_reg_block" (but we need to add that name to
  // ral_model_names so that it can be found)
  string rom_ral_name = inherit_ral_models ? m_chip_level_rom_ral_name : m_block_level_rom_ral_name;

  ral_model_names[rom_ral_name] = 1'b0;

  super.initialize(inherit_ral_models);

  // default TLUL supports 1 outstanding item, the rom TLUL supports 2 outstanding items.
  m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 1;
  m_tl_agent_cfgs[rom_ral_name].max_outstanding_req = 2;

  // Tell the CIP base code what bit gets set if we see a TL fault.
  tl_intg_alert_fields[ral.fatal_alert_cause.integrity_error] = 1;

  // Default is 10ms (see default_spinwait_timeout_ns in csr_utils_pkg.sv, assigned in
  // cip_base_env_cfg)
  // We have to increase this here since the ROM check may actually take longer than that,
  // which sometimes causes blocked TL accesses to time out.
  tl_access_timeout_ns = 40_000_000; // 40ms
endfunction

// Override the default implementation in dv_base_env_cfg.
//
// This is required for the ROM environment for reuse at the chip level as 2 different
// parameterizations of the design and testbench exist, as a result the custom RAL model for the
// ROM memory primitive must also be explicitly parameterized.
//
// We cannot instantiate parameterized UVM objects/components using the standard factory
// mechanisms, so a custom instantiation method is required here.
//
// Note that the ROM only has 2 RAL models, one is the "default" CSR model,
// and the other is the custom model to represent the memory primitive.
function dv_base_reg_block rom_ctrl_env_cfg::create_ral_by_name(string name);
  if (name == RAL_T::type_name) begin
    return super.create_ral_by_name(name);
  end else if (name == m_block_level_rom_ral_name) begin
    return rom_ctrl_prim_reg_block#(ROM_SIZE_WORDS)::type_id::create(m_block_level_rom_ral_name);
  end else begin
    `uvm_error(`gfn, $sformatf("%0s is an illegal RAL model name", name))
  end
endfunction

function bit rom_ctrl_env_cfg::get_skip_middle();
  return m_skip_middle;
endfunction

function bit rom_ctrl_env_cfg::is_rom_ral_name(string ral_name);
  return (ral_name inside {m_block_level_rom_ral_name, m_chip_level_rom_ral_name});
endfunction

function uvm_mem rom_ctrl_env_cfg::get_rom_ral();
  uvm_reg_block block;
  uvm_mem       mems[$];

  if (ral_models.exists(m_block_level_rom_ral_name)) begin
    block = ral_models[m_block_level_rom_ral_name];
  end else if (ral_models.exists(m_chip_level_rom_ral_name)) begin
    block = ral_models[m_chip_level_rom_ral_name];
  end else begin
    `uvm_fatal("no_ral", "Cannot find a RAL for the interface with ROM.")
  end

  block.get_memories(mems);

  if (mems.size() != 1) begin
    `uvm_error("not_one_mem",
               $sformatf("The set of memories for block %0s has size %0d (not 1).",
                         block.get_name(), mems.size()))
  end

  return mems[0];
endfunction

function int unsigned rom_ctrl_env_cfg::get_rom_size_bytes();
  uvm_mem mem = get_rom_ral();

  return mem.get_size() * mem.get_n_bits() / 8;
endfunction

function bit [DIGEST_SIZE-1:0] rom_ctrl_env_cfg::get_expected_digest();
  bit [DIGEST_SIZE-1:0] digest;

  // Read the size of ROM in bytes and divide by 4 to get the number of 32-bit words. Then subtract
  // DIGEST_SIZE/32 to get the index of first 32-bit word of the digest. This digest sits in the top
  // DIGEST_SIZE bits of the ROM.
  int unsigned dig_addr = get_rom_size_bytes() / 4 - DIGEST_SIZE / 32;

  // Backdoor load the digest in 32-bit words.
  for (int unsigned i = 0; i < DIGEST_SIZE / 32; i++) begin
    bit [38:0] raw_word = rom_ctrl_bkdr_util_h.rom_encrypt_read32(4 * (dig_addr + i),
                                                                  m_scramble_key,
                                                                  m_scramble_nonce,
                                                                  1'b0);

    // Ignore the top 6 bits (which contain ECC data) and just accumulate the other 32.
    digest[32 * i +: 32] = raw_word[31:0];
  end

  return digest;
endfunction

constraint rom_ctrl_env_cfg::rsp_delay_max_c {
  // Note that this doesn't involve m_kmac_agent_cfg.zero_delays. If that bit is set, the agent will
  // ignore its rsp_delay_max field (copied from this value in post_randomize), so this variable
  // will have no effect.
  m_kmac_rsp_delay_max dist { 1 :/ 10, 10 :/ 1 };
}
