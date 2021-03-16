// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env_cfg extends cip_base_env_cfg #(.RAL_T(entropy_src_reg_block));

  `uvm_object_utils_begin(entropy_src_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // Ext component cfgs
  rand push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))
       m_rng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
       m_csrng_agent_cfg;

  virtual pins_if  efuse_es_sw_reg_en_vif;

  // Knobs & Weights
  uint            efuse_es_sw_reg_en_pct, enable_lfsr_pct, enable_ptrng_pct, route_software_pct,
                  type_bypass_pct;
  rand bit        efuse_es_sw_reg_en, route_software, type_bypass;
  rand enable_e   enable;

  // Constraints
  constraint c_efuse_es_sw_reg_en {efuse_es_sw_reg_en dist { 1 :/ efuse_es_sw_reg_en_pct,
                                                             0 :/ (100 - efuse_es_sw_reg_en_pct) };}

  constraint c_enable {
     enable dist { LFSR_Mode :/ enable_lfsr_pct, PTRNG_Mode :/ enable_ptrng_pct,
                   Disable :/ 100 - enable_lfsr_pct - enable_ptrng_pct };
  }

  constraint c_route {route_software dist { 1 :/ route_software_pct,
                                            0 :/ (100 - route_software_pct) };}

  constraint c_bypass {type_bypass dist { 1 :/ type_bypass_pct,
                                          0 :/ (100 - type_bypass_pct) };}

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
    str = {str,  $sformatf("\n\t |********** entropy_src_env_cfg ****************| \t")                  };
    str = {str,  $sformatf("\n\t |***** efuse_es_sw_reg_en     : %10d *****| \t", efuse_es_sw_reg_en)    };
    str = {str,  $sformatf("\n\t |***** enable                 : %10s *****| \t", enable.name())         };
    str = {str,  $sformatf("\n\t |***** route_software         : %10d *****| \t", route_software)        };
    str = {str,  $sformatf("\n\t |---------- knobs ------------------------------| \t")                  };
    str = {str,  $sformatf("\n\t |***** efuse_es_sw_reg_en_pct : %10d *****| \t", efuse_es_sw_reg_en_pct)};
    str = {str,  $sformatf("\n\t |***** enable_lfsr_pct        : %10d *****| \t", enable_lfsr_pct)       };
    str = {str,  $sformatf("\n\t |***** enable_ptrng_pct       : %10d *****| \t", enable_ptrng_pct)      };
    str = {str,  $sformatf("\n\t |***** route_software_pct     : %10d *****| \t", route_software_pct)    };
    str = {str,  $sformatf("\n\t |***** type_bypass_pct        : %10d *****| \t", type_bypass_pct)       };
    str = {str,  $sformatf("\n\t |***********************************************| \t")                  };
    str = {str, "\n"};
    return str;
  endfunction

endclass
