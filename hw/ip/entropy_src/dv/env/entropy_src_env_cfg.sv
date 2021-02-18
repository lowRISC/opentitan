// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env_cfg extends cip_base_env_cfg #(.RAL_T(entropy_src_reg_block));

  `uvm_object_utils_begin(entropy_src_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // Ext component cfgs
  rand push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))  m_rng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))  m_csrng_agent_cfg;

  virtual pins_if  efuse_es_sw_reg_en_vif;

  // Knobs & Weights
  uint      efuse_es_sw_reg_en_pct;
  rand bit  efuse_es_sw_reg_en;

  // Constraints
  constraint c_efuse_es_sw_reg_en {efuse_es_sw_reg_en dist { 1 :/ efuse_es_sw_reg_en_pct,
                                                             0 :/ (100 - efuse_es_sw_reg_en_pct) };}

  // Functions
  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = entropy_src_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    // create agent config objs
    m_rng_agent_cfg   = push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))::
                        type_id::create("m_rng_agent_cfg");
    m_csrng_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))::
                        type_id::create("m_csrng_agent_cfg");

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
    str = {str,  $sformatf("\n\t |********** entropy_src_env_cfg **********| \t")                        };
    str = {str,  $sformatf("\n\t |***** efuse_es_sw_reg_en      : %3d *****| \t", efuse_es_sw_reg_en)    };
    str = {str,  $sformatf("\n\t |---------- knobs ------------------------| \t")                        };
    str = {str,  $sformatf("\n\t |***** efuse_es_sw_reg_en_pct  : %3d *****| \t", efuse_es_sw_reg_en_pct)};
    str = {str,  $sformatf("\n\t |*****************************************| \t")                        };
    str = {str, "\n"};
    return str;
  endfunction

endclass
