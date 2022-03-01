// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_env_cfg extends cip_base_env_cfg #(.RAL_T(edn_reg_block));

  // external component cfgs
  csrng_agent_cfg   m_csrng_agent_cfg;
  push_pull_agent_cfg#(.HostDataWidth(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH))
      m_endpoint_agent_cfg[MAX_NUM_ENDPOINTS];

  `uvm_object_utils_begin(edn_env_cfg)
    `uvm_field_object(m_csrng_agent_cfg, UVM_DEFAULT)
    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      `uvm_field_object(m_endpoint_agent_cfg[i], UVM_DEFAULT)
    end
  `uvm_object_utils_end
  `uvm_object_new

  // Knobs & Weights
  uint   enable_pct, boot_req_mode_pct, auto_req_mode_pct,
         min_num_boot_reqs, max_num_boot_reqs,
         min_num_ep_reqs, max_num_ep_reqs;

  rand mubi4_t   enable, boot_req_mode, auto_req_mode;
  rand uint      num_endpoints, num_boot_reqs;
  rand bit[csrng_pkg::CSRNG_CMD_WIDTH - 1:0]   boot_ins_cmd, boot_gen_cmd;

  // Constraints
  // TODO: utilize suggestions in PR9535 to generate "other" values when testing alerts
  constraint enable_c {enable dist {
    MuBi4True  :/ enable_pct,
    MuBi4False :/ (100 - enable_pct) };}

  constraint num_endpoints_c {num_endpoints dist {
    MIN_NUM_ENDPOINTS :/ 40,
    MAX_NUM_ENDPOINTS :/ 40,
    [MIN_NUM_ENDPOINTS + 1:MAX_NUM_ENDPOINTS - 1] :/ 20 };}

  constraint req_mode_c {{boot_req_mode, auto_req_mode} dist {
    {MuBi4True, MuBi4False}  :/ boot_req_mode_pct,
    {MuBi4False, MuBi4True}  :/ auto_req_mode_pct,
    {MuBi4False, MuBi4False} :/ (100 - boot_req_mode_pct - auto_req_mode_pct) };

    if (boot_req_mode == MuBi4True) {
      num_boot_reqs inside { [min_num_boot_reqs:max_num_boot_reqs] };
    }
    else {
      num_boot_reqs == 0;}}

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = edn_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create config objects
    m_csrng_agent_cfg = csrng_agent_cfg::type_id::create("m_csrng_genbits_agent_cfg");

    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      m_endpoint_agent_cfg[i] = push_pull_agent_cfg#(.HostDataWidth(edn_pkg::
                                FIPS_ENDPOINT_BUS_WIDTH))::type_id::create
                                ($sformatf("m_endpoint_agent_cfg[%0d]", i));
    end

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |******************* edn_env_cfg *********************| \t")};
    str = {str,  $sformatf("\n\t |***** enable                       : %10s *****| \t",
        enable.name())};
    str = {str,  $sformatf("\n\t |***** boot_req_mode                : %10s *****| \t",
        boot_req_mode.name())};
    str = {str,  $sformatf("\n\t |***** auto_req_mode                : %10s *****| \t",
        auto_req_mode.name())};
    str = {str,  $sformatf("\n\t |***** num_endpoints                : %10d *****| \t",
        num_endpoints)};
    str = {str,  $sformatf("\n\t |***** num_boot_reqs                : %10d *****| \t",
        num_boot_reqs)};
    str = {str,  $sformatf("\n\t |------------------- knobs ---------------------------| \t")};
    str = {str,  $sformatf("\n\t |***** enable_pct                   : %10d *****| \t",
        enable_pct)};
    str = {str,  $sformatf("\n\t |***** boot_req_mode_pct            : %10d *****| \t",
        boot_req_mode_pct)};
    str = {str,  $sformatf("\n\t |***** auto_req_mode_pct            : %10d *****| \t",
        auto_req_mode_pct)};
    str = {str,  $sformatf("\n\t |***** MAX_NUM_ENDPOINTS            : %10d *****| \t",
        MAX_NUM_ENDPOINTS)};
    str = {str,  $sformatf("\n\t |***** min_num_boot_reqs            : %10d *****| \t",
        min_num_boot_reqs)};
    str = {str,  $sformatf("\n\t |***** max_num_boot_reqs            : %10d *****| \t",
        max_num_boot_reqs)};
    str = {str,  $sformatf("\n\t |*****************************************************| \t")};
    str = {str, "\n"};
    return str;
  endfunction

endclass
