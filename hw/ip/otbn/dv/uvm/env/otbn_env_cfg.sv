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

endclass
