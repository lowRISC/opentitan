// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_env_cfg extends cip_base_env_cfg #(.RAL_T(otbn_reg_block));

  // ext component cfgs
  rand otbn_model_agent_cfg model_agent_cfg;

  `uvm_object_utils_begin(otbn_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual otbn_trace_if      trace_vif;
  virtual otbn_loop_if       loop_vif;
  virtual otbn_alu_bignum_if alu_bignum_vif;
  virtual otbn_mac_bignum_if mac_bignum_vif;
  virtual otbn_rf_base_if    rf_base_vif;
  virtual otbn_controller_if controller_vif;

  mem_bkdr_util imem_util;
  mem_bkdr_util dmem_util;

  // The directory in which to look for ELF files (set by the test in build_phase; controlled by the
  // +otbn_elf_dir plusarg).
  string otbn_elf_dir;

  // An OtbnMemUtil handle for loading ELF files (set by the test in build_phase)
  chandle mem_util;

  // What fraction of the time should sequences use a back-door method to load up the ELF, rather
  // than generating memory transactions?
  int unsigned backdoor_load_pct = 50;

  // The hierarchical scope of the DUT instance in the testbench. This is used when constructing the
  // DPI wrapper (in otbn_env::build_phase) to tell it where to find the DUT for backdoor loading
  // memories. The default value matches the block-level testbench, but it can be overridden in a
  // test class for e.g. system level tests.
  string dut_instance_hier = "tb.dut";

  // Copied from dv_base_agent_cfg so that we can use a monitor without defining a separate agent.
  int ok_to_end_delay_ns = 1000;

  function void initialize(bit [31:0] csr_base_addr = '1);
    has_edn = 1;
    // Tell the CIP base code not to look for a "devmode" interface. OTBN doesn't have one.
    has_devmode = 0;

    // Set the list of alerts, needed by the CIP base code. This needs to match the names assigned
    // in tb.sv (where we bind in the alert interfaces and register each with the UVM DB).
    list_of_alerts = otbn_env_pkg::LIST_OF_ALERTS;

    // Tell the CIP base code how many interrupts we have (defaults to zero)
    num_interrupts = 1;

    // Tell the CIP base code what alert we generate if we see a TL fault.
    tl_intg_alert_name = "fatal";

    model_agent_cfg = otbn_model_agent_cfg::type_id::create("model_agent_cfg");

    super.initialize(csr_base_addr);

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

  function logic [63:0] get_imem_nonce();
    logic [63:0] nonce;
    string       nonce_hier = $sformatf("%s.u_imem.nonce_i", dut_instance_hier);
    `DV_CHECK_FATAL(uvm_hdl_read(nonce_hier, nonce), "Failed to read nonce from IMEM instance")
    return nonce;
  endfunction

  // Read a word from IMEM, descrambling but including integrity bits.
  function logic [38:0] read_imem_word(bit [ImemIndexWidth-1:0] idx,
                                       logic [127:0]            key,
                                       logic [63:0]             nonce);

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
    clr_data_arr = sram_scrambler_pkg::decrypt_sram_data(scr_data_arr, 39, 1'b0,
                                                         idx_arr, ImemIndexWidth,
                                                         key_arr, nonce_arr);
    clr_data = {<<{clr_data_arr}};

    return clr_data;
  endfunction

  // Scramble and write a word to IMEM (including integrity bits)
  function void write_imem_word(bit [ImemIndexWidth-1:0] idx,
                                logic [38:0]             clr_data,
                                logic [127:0]            key,
                                logic [63:0]             nonce);

    logic [ImemIndexWidth-1:0] phys_idx;
    logic [38:0]               scr_data;

    logic key_arr[], nonce_arr[], idx_arr[], phys_idx_arr[], scr_data_arr[], clr_data_arr[];

    key_arr = new[128]; key_arr = {<<{key}};
    nonce_arr = new[64]; nonce_arr = {<<{nonce}};
    idx_arr = new[ImemIndexWidth]; idx_arr = {<<{idx}};

    // Scramble the index to find the word in physical memory
    phys_idx_arr = sram_scrambler_pkg::encrypt_sram_addr(idx_arr, ImemIndexWidth, nonce_arr);
    phys_idx = {<<{phys_idx_arr}};

    // Scramble the data
    clr_data_arr = {<<{clr_data}};
    scr_data_arr = sram_scrambler_pkg::encrypt_sram_data(clr_data_arr, 39, 1'b0,
                                                         idx_arr, ImemIndexWidth,
                                                         key_arr, nonce_arr);
    scr_data = {<<{scr_data_arr}};

    // Write the scrambled data to memory
    imem_util.write(BUS_AW'(phys_idx) * 4, scr_data);
  endfunction

endclass
