// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_env_cfg extends cip_base_env_cfg #(.RAL_T(edn_reg_block));

  // ext component cfgs
  rand csrng_agent_cfg   m_csrng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH))
            m_endpoint_agent_cfg [NUM_ENDPOINTS:0];

  `uvm_object_utils_begin(edn_env_cfg)
    `uvm_field_object(m_csrng_agent_cfg, UVM_DEFAULT)
    for (int i = 0; i < NUM_ENDPOINTS; i++) begin
      `uvm_field_object(m_endpoint_agent_cfg[i], UVM_DEFAULT)
    end
  `uvm_object_utils_end

  `uvm_object_new

  // Knobs & Weights
  uint   enable_pct, boot_req_mode_pct, auto_req_mode_pct;

  rand bit[3:0]   enable;
  rand bit[3:0]   boot_req_mode;
  rand bit[3:0]   auto_req_mode;

  // Constraints
  constraint c_enable {enable dist {
                       edn_pkg::EDN_FIELD_ON         :/ enable_pct,
                       [0:edn_pkg::EDN_FIELD_ON - 1] :/ (100 - enable_pct)/2,
                       [edn_pkg::EDN_FIELD_ON + 1:$] :/ (100 - enable_pct)/2 };}
  constraint c_boot_req_mode {boot_req_mode dist {
                              edn_pkg::EDN_FIELD_ON :/ boot_req_mode_pct,
                              [0:edn_pkg::EDN_FIELD_ON - 1] :/ (100 - boot_req_mode_pct)/2,
                              [edn_pkg::EDN_FIELD_ON + 1:$] :/ (100 - boot_req_mode_pct)/2 };}
  constraint c_auto_req_mode {auto_req_mode dist {
                              [0:edn_pkg::EDN_FIELD_ON - 1] :/ (100 - auto_req_mode_pct)/2,
                              [edn_pkg::EDN_FIELD_ON + 1:$] :/ (100 - auto_req_mode_pct)/2 };}

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = edn_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);
    // create config objects
    m_csrng_agent_cfg = csrng_agent_cfg::type_id::create("m_csrng_genbits_agent_cfg");

    for (int i = 0; i < NUM_ENDPOINTS; i++) begin
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
    str = {str,  $sformatf("\n\t |************** edn_env_cfg *******************| \t")              };
    str = {str,  $sformatf("\n\t |***** enable                : %10d *****| \t", enable)            };
    str = {str,  $sformatf("\n\t |***** boot_req_mode         : %10d *****| \t", boot_req_mode)     };
    str = {str,  $sformatf("\n\t |***** auto_req_mode         : %10d *****| \t", auto_req_mode)     };
    str = {str,  $sformatf("\n\t |---------- knobs -----------------------------| \t")              };
    str = {str,  $sformatf("\n\t |***** enable_pct            : %10d *****| \t", enable_pct)        };
    str = {str,  $sformatf("\n\t |***** boot_req_mode_pct     : %10d *****| \t", boot_req_mode_pct) };
    str = {str,  $sformatf("\n\t |***** auto_req_mode_pct     : %10d *****| \t", auto_req_mode_pct) };
    str = {str,  $sformatf("\n\t |**********************************************| \t")              };
    str = {str, "\n"};
    return str;
  endfunction

endclass
