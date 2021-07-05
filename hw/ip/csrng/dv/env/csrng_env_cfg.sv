// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_env_cfg extends cip_base_env_cfg #(.RAL_T(csrng_reg_block));

  `uvm_object_utils_begin(csrng_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // ext component cfgs
  rand push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))
       m_entropy_src_agent_cfg;

  rand csrng_agent_cfg   m_edn_agent_cfg;

  virtual pins_if  efuse_sw_app_enable_vif;

  // Knobs & Weights
  uint             efuse_sw_app_enable_pct, aes_cipher_disable_pct,
                   cmd_length_0_pct, cmd_flags_0_pct, chk_int_state_pct;
  rand bit         efuse_sw_app_enable, aes_cipher_disable, chk_int_state;
  rand bit [3:0]   cmd_length, cmd_flags;

  // Variables
  bit [csrng_env_pkg::KEY_LEN-1:0]       key;
  bit [csrng_env_pkg::BLOCK_LEN-1:0]     v;
  bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   reseed_counter;

  // Constraints
  constraint c_efuse_sw_app_enable {efuse_sw_app_enable dist { 1 :/ efuse_sw_app_enable_pct,
                                                               0 :/ (100 - efuse_sw_app_enable_pct)
                                                             };}

  constraint c_aes_cipher_disable {aes_cipher_disable dist { 1 :/ aes_cipher_disable_pct,
                                                             0 :/ (100 - aes_cipher_disable_pct)
                                                           };}

  constraint c_chk_int_state {chk_int_state dist { 1 :/ chk_int_state_pct,
                                                   0 :/ (100 - chk_int_state_pct)
                                                 };}

  constraint c_cmd_length_0 {cmd_length dist { 0      :/ cmd_length_0_pct,
                                               [1:12] :/ (100 - cmd_length_0_pct)
                                             };}

  constraint c_cmd_flags_0 {cmd_flags dist { 0 :/ cmd_flags_0_pct,
                                             1 :/ (100 - cmd_flags_0_pct)
                                           };}

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = csrng_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create agent configs
    m_entropy_src_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::
                              FIPS_CSRNG_BUS_WIDTH))::type_id::create("m_entropy_src_agent_cfg");

    m_edn_agent_cfg = csrng_agent_cfg::type_id::create("m_edn_agent_cfg");

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
    str = {str,  $sformatf("\n\t |********** csrng_env_cfg ***********************| \t")                    };
    str = {str,  $sformatf("\n\t |***** efuse_sw_app_enable     : %10d *****| \t", efuse_sw_app_enable)     };
    str = {str,  $sformatf("\n\t |***** aes_cipher_disable      : %10d *****| \t", aes_cipher_disable)      };
    str = {str,  $sformatf("\n\t |***** chk_int_state           : %10d *****| \t", chk_int_state)           };
    str = {str,  $sformatf("\n\t |***** cmd_length              : %10d *****| \t", cmd_length)              };
    str = {str,  $sformatf("\n\t |***** cmd_flags               : %10d *****| \t", cmd_flags)               };
    str = {str,  $sformatf("\n\t |---------- knobs -------------------------------| \t")                    };
    str = {str,  $sformatf("\n\t |***** efuse_sw_app_enable_pct : %10d *****| \t", efuse_sw_app_enable_pct) };
    str = {str,  $sformatf("\n\t |***** aes_cipher_disable_pct  : %10d *****| \t", aes_cipher_disable_pct)  };
    str = {str,  $sformatf("\n\t |***** chk_int_state_pct       : %10d *****| \t", chk_int_state_pct)       };
    str = {str,  $sformatf("\n\t |***** cmd_length_0_pct        : %10d *****| \t", cmd_length_0_pct)        };
    str = {str,  $sformatf("\n\t |***** cmd_flags_0_pct         : %10d *****| \t", cmd_flags_0_pct)         };
    str = {str,  $sformatf("\n\t |************************************************| \t")                    };
    str = {str, "\n"};
    return str;
  endfunction

endclass
