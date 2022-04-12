// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_env_cfg extends cip_base_env_cfg #(.RAL_T(otbn_reg_block));

  // ext component cfgs
  rand otbn_model_agent_cfg model_agent_cfg;

  rand otbn_sideload_agent_cfg keymgr_sideload_agent_cfg;

  rand otp_key_agent_cfg key_cfg;

  virtual clk_rst_if otp_clk_rst_vif;

  `uvm_object_utils_begin(otbn_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual otbn_trace_if      trace_vif;
  virtual otbn_loop_if       loop_vif;
  virtual otbn_alu_bignum_if alu_bignum_vif;
  virtual otbn_mac_bignum_if mac_bignum_vif;
  virtual otbn_rf_base_if    rf_base_vif;
  virtual otbn_escalate_if   escalate_vif;

  mem_bkdr_util imem_util;
  mem_bkdr_util dmem_util;

  // A handle to the scoreboard, used to flag expected errors.
  otbn_scoreboard scoreboard;

  // The directory in which to look for ELF files (set by the test in build_phase; controlled by the
  // +otbn_elf_dir plusarg).
  string otbn_elf_dir;

  // An OtbnMemUtil handle for loading ELF files (set by the test in build_phase)
  chandle mem_util;

  // What fraction of the time should sequences use a back-door method to load up the ELF, rather
  // than generating memory transactions?
  int unsigned backdoor_load_pct = 50;

  // How often should sequences enable interrupts?
  int unsigned enable_interrupts_pct = 50;

  // If a previous sequence triggered an interrupt, should we clear it again before we start?
  int unsigned clear_irq_pct = 90;

  // How often should we poll STATUS to detect completion, even though interrupts are enabled?
  int unsigned poll_despite_interrupts_pct = 10;

  // Should we allow the sideload key not to be valid? If we do, we have to disable the exp_end_addr
  // check (since we might stop in the middle of the operation by reading from the sideload key WSR
  // when it isn't available).
  int unsigned allow_no_sideload_key_pct = 50;

  // The hierarchical scope of the DUT instance in the testbench. This is used when constructing the
  // DPI wrapper (in otbn_env::build_phase) to tell it where to find the DUT for backdoor loading
  // memories. The default value matches the block-level testbench, but it can be overridden in a
  // test class for e.g. system level tests.
  string dut_instance_hier = "tb.dut";

  // Copied from dv_base_agent_cfg so that we can use a monitor without defining a separate agent.
  int ok_to_end_delay_ns = 1000;

  // otp clk freq
  rand uint otp_freq_mhz;
  constraint otp_freq_mhz_c {
    `DV_COMMON_CLK_CONSTRAINT(otp_freq_mhz)
  }

  function void initialize(bit [31:0] csr_base_addr = '1);
    num_edn = 2;
    // Tell the CIP base code not to look for a "devmode" interface. OTBN doesn't have one.
    has_devmode = 0;

    // Set the list of alerts, needed by the CIP base code. This needs to match the names assigned
    // in tb.sv (where we bind in the alert interfaces and register each with the UVM DB).
    list_of_alerts = otbn_env_pkg::LIST_OF_ALERTS;

    // Tell the CIP base code how many interrupts we have (defaults to zero)
    num_interrupts = 1;

    // Tell the CIP base code what alert we generate if we see a TL or sec cm fault.
    tl_intg_alert_name = "fatal";
    sec_cm_alert_name = "fatal";

    model_agent_cfg  = otbn_model_agent_cfg  ::type_id::create("model_agent_cfg");
    keymgr_sideload_agent_cfg = otbn_sideload_agent_cfg::type_id::create(
      "keymgr_sideload_agent_cfg");


    // Build OTP Key cfg object
    key_cfg = otp_key_agent_cfg::type_id::create("key_cfg");

    super.initialize(csr_base_addr);

    // We can only have one outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;

    // Tell the CIP base code the fields that it should expect to see, together with their expected
    // values, in case of a TL fault.
    tl_intg_alert_fields[ral.fatal_alert_cause.bus_intg_violation] = 1;
    tl_intg_alert_fields[ral.status.status] = otbn_pkg::StatusLocked;
  endfunction

  function logic [127:0] get_imem_key();
    logic [127:0] key;
    string        key_hier = $sformatf("%s.u_imem.key_i", dut_instance_hier);
    `DV_CHECK_FATAL(uvm_hdl_read(key_hier, key), "Failed to read key from IMEM instance")
    return key;
  endfunction

  function logic [127:0] get_dmem_key();
    logic [127:0] key;
    string        key_hier = $sformatf("%s.u_dmem.key_i", dut_instance_hier);
    `DV_CHECK_FATAL(uvm_hdl_read(key_hier, key), "Failed to read key from DMEM instance")
    return key;
  endfunction

  function logic [63:0] get_imem_nonce();
    logic [63:0] nonce;
    string       nonce_hier = $sformatf("%s.u_imem.nonce_i", dut_instance_hier);
    `DV_CHECK_FATAL(uvm_hdl_read(nonce_hier, nonce), "Failed to read nonce from IMEM instance")
    return nonce;
  endfunction

  function logic [63:0] get_dmem_nonce();
    logic [63:0] nonce;
    string       nonce_hier = $sformatf("%s.u_dmem.nonce_i", dut_instance_hier);
    `DV_CHECK_FATAL(uvm_hdl_read(nonce_hier, nonce), "Failed to read nonce from DMEM instance")
    return nonce;
  endfunction

  // Read a word from IMEM, descrambling but including integrity bits.
  function logic [38:0] read_imem_word(bit [ImemIndexWidth-1:0]    idx,
                                       logic [127:0]               key,
                                       otbn_pkg::otbn_imem_nonce_t nonce);

    logic [ImemIndexWidth-1:0] phys_idx;
    logic [38:0]               scr_data, clr_data;

    logic key_arr[], nonce_arr[], idx_arr[], phys_idx_arr[], scr_data_arr[], clr_data_arr[];

    key_arr = new[128]; key_arr = {<<{key}};
    nonce_arr = new[64]; nonce_arr = {<<{nonce}};
    idx_arr = new[ImemIndexWidth]; idx_arr = {<<{idx}};

    // Scramble the index to find the word in physical memory
    phys_idx_arr = sram_scrambler_pkg::encrypt_sram_addr(idx_arr, ImemIndexWidth, nonce_arr);
    phys_idx = {<<{phys_idx_arr}};

    // Read the memory at that location to get scrambled data
    scr_data = imem_util.read(BUS_AW'(phys_idx) * 4);
    scr_data_arr = {<<{scr_data}};

    // Descramble the data
    clr_data_arr = sram_scrambler_pkg::decrypt_sram_data(scr_data_arr, 39, 39,
                                                         idx_arr, ImemIndexWidth,
                                                         key_arr, nonce_arr);
    clr_data = {<<{clr_data_arr}};

    return clr_data;
  endfunction

  // Read a word from DMEM, descrambling but including integrity bits.
  function logic [311:0] read_dmem_word(bit [DmemIndexWidth-1:0]    idx,
                                        logic [127:0]               key,
                                        otbn_pkg::otbn_dmem_nonce_t nonce);

    logic [DmemIndexWidth-1:0] phys_idx;
    logic [311:0]              scr_data, clr_data;

    logic key_arr[], nonce_arr[], idx_arr[], phys_idx_arr[], scr_data_arr[], clr_data_arr[];

    key_arr = new[128]; key_arr = {<<{key}};
    nonce_arr = new[64]; nonce_arr = {<<{nonce}};
    idx_arr = new[DmemIndexWidth]; idx_arr = {<<{idx}};

    // Scramble the index to find the word in physical memory
    phys_idx_arr = sram_scrambler_pkg::encrypt_sram_addr(idx_arr, DmemIndexWidth, nonce_arr);
    phys_idx = {<<{phys_idx_arr}};

    // Read the memory at that location to get scrambled data
    scr_data = dmem_util.read(BUS_AW'(phys_idx) * 32);
    scr_data_arr = {<<{scr_data}};

    // Descramble the data
    clr_data_arr = sram_scrambler_pkg::decrypt_sram_data(scr_data_arr, 312, 39,
                                                         idx_arr, DmemIndexWidth,
                                                         key_arr, nonce_arr);
    clr_data = {<<{clr_data_arr}};
    return clr_data;
  endfunction

  // Scramble and write a word to IMEM (including integrity bits)
  function void write_imem_word(bit [ImemIndexWidth-1:0]           idx,
                                logic [38:0]                       clr_data,
                                logic [127:0]                      key,
                                otbn_pkg::otbn_imem_nonce_t        nonce,
                                bit   [38:0]                       flip_bits = 0);

    logic [ImemIndexWidth-1:0] phys_idx;
    logic [38:0]               scr_data;
    logic [38:0]               integ_data;

    logic key_arr[], nonce_arr[], idx_arr[], phys_idx_arr[], scr_data_arr[], clr_data_arr[];

    key_arr = new[128]; key_arr = {<<{key}};
    nonce_arr = new[64]; nonce_arr = {<<{nonce}};
    idx_arr = new[ImemIndexWidth]; idx_arr = {<<{idx}};

    // Scramble the index to find the word in physical memory
    phys_idx_arr = sram_scrambler_pkg::encrypt_sram_addr(idx_arr, ImemIndexWidth, nonce_arr);
    phys_idx = {<<{phys_idx_arr}};

    // flip some bits to inject integrity fault
    clr_data ^= flip_bits;

    // Scramble the data
    clr_data_arr = {<<{clr_data}};
    scr_data_arr = sram_scrambler_pkg::encrypt_sram_data(clr_data_arr, 39, 39,
                                                         idx_arr, ImemIndexWidth,
                                                         key_arr, nonce_arr);
    scr_data = {<<{scr_data_arr}};

    // Write the scrambled data to memory
    imem_util.write(BUS_AW'(phys_idx) * 4, scr_data);
  endfunction

  // Scramble and write a word to DMEM (including integrity bits)
  function void write_dmem_word(bit [DmemIndexWidth-1:0]    idx,
                                logic [311:0]               clr_data,
                                logic [127:0]               key,
                                otbn_pkg::otbn_dmem_nonce_t nonce,
                                bit   [311:0]               flip_bits = 0);

    logic [DmemIndexWidth-1:0] phys_idx;
    bit [311:0]               scr_data;

    logic key_arr[], nonce_arr[], idx_arr[], phys_idx_arr[], scr_data_arr[], clr_data_arr[];

    key_arr = new[128]; key_arr = {<<{key}};
    nonce_arr = new[64]; nonce_arr = {<<{nonce}};
    idx_arr = new[DmemIndexWidth]; idx_arr = {<<{idx}};

    // Scramble the index to find the word in physical memory
    phys_idx_arr = sram_scrambler_pkg::encrypt_sram_addr(idx_arr, DmemIndexWidth, nonce_arr);
    phys_idx = {<<{phys_idx_arr}};
    // flip some bits to inject integrity fault
    clr_data ^= flip_bits;

    // Scramble the data
    clr_data_arr = {<<{clr_data}};
    scr_data_arr = sram_scrambler_pkg::encrypt_sram_data(clr_data_arr, 312, 39,
                                                         idx_arr, DmemIndexWidth,
                                                         key_arr, nonce_arr);
    scr_data = {<<{scr_data_arr}};

    // Write the scrambled data to memory
    dmem_util.write(BUS_AW'(phys_idx) * 32, scr_data);
  endfunction

  // Strip off integrity bits from IMEM
  function logic [31:0] strip_integrity_32(logic [BaseIntgWidth-1:0] data);
    return data[31:0];
  endfunction

  // Add new known-good integrity bits to data
  function logic [BaseIntgWidth-1:0] add_integrity_32(logic [31:0] data);
    return prim_secded_pkg::prim_secded_inv_39_32_enc(data);
  endfunction

  // Fix integrity bits of data
  function logic [BaseIntgWidth-1:0] fix_integrity_32(logic [BaseIntgWidth-1:0] data);
    return add_integrity_32(strip_integrity_32(data));
  endfunction

  // Strip off integrity bits from data
  function logic [WLEN-1:0] strip_integrity_wlen(logic [ExtWLEN-1:0] data);
    logic [WLEN-1:0] ret;
    for (int i = 0; i < 8; ++i) begin
      ret[32*i +: 32] = strip_integrity_32(data[39*i +: 39]);
    end
    return ret;
  endfunction

  // Add new known-good integrity bits to data
  function logic [ExtWLEN-1:0] add_integrity_wlen(logic [WLEN-1:0] data);
    logic [ExtWLEN-1:0] ret;
    for (int i = 0; i < 8; ++i) begin
      ret[39*i +: 39] = add_integrity_32(data[32*i +: 32]);
    end
    return ret;
  endfunction

  // Fix integrity bits of data
  function logic [ExtWLEN-1:0] fix_integrity_wlen(logic [ExtWLEN-1:0] data);
    return add_integrity_wlen(strip_integrity_wlen(data));
  endfunction

endclass
