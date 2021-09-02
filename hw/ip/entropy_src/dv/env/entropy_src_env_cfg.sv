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

  virtual pins_if#(8)   otp_en_es_fw_read_vif;
  virtual pins_if#(8)   otp_en_es_fw_over_vif;

  // Knobs & Weights
  uint          enable_pct, route_software_pct,
                otp_en_es_fw_read_pct, otp_en_es_fw_over_pct,
                type_bypass_pct, boot_bypass_disable_pct;
  rand bit      enable, route_software, type_bypass,
                boot_bypass_disable;

  rand otp_ctrl_pkg::otp_en_t   otp_en_es_fw_read, otp_en_es_fw_over;

  // Constraints
  constraint c_otp_en_es_fw_read {otp_en_es_fw_read dist {
                                  otp_ctrl_pkg::Enabled  :/ otp_en_es_fw_read_pct,
                                  otp_ctrl_pkg::Disabled :/ (100 - otp_en_es_fw_read_pct) };}

  constraint c_otp_en_es_fw_over {otp_en_es_fw_over dist {
                                  otp_ctrl_pkg::Enabled  :/ otp_en_es_fw_over_pct,
                                  otp_ctrl_pkg::Disabled :/ (100 - otp_en_es_fw_over_pct) };}

  constraint c_enable {enable dist { 1 :/ enable_pct,
                                     0 :/ 100 - enable_pct };
  }

  constraint c_route {route_software dist { 1 :/ route_software_pct,
                                            0 :/ (100 - route_software_pct) };}

  constraint c_bypass {type_bypass dist { 1 :/ type_bypass_pct,
                                          0 :/ (100 - type_bypass_pct) };}

  constraint c_boot_bypass_disable {boot_bypass_disable dist { 1 :/ boot_bypass_disable_pct,
                                                               0 :/ (100 - boot_bypass_disable_pct)
                                                             };}

  // Functions
  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = entropy_src_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
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
    str = {str,  $sformatf("\n\t |************ entropy_src_env_cfg ****************| \t")                    };
    str = {str,  $sformatf("\n\t |***** enable                   : %10d *****| \t", enable)                  };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_read        : %10d *****| \t", otp_en_es_fw_read)       };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_over        : %10d *****| \t", otp_en_es_fw_over)       };
    str = {str,  $sformatf("\n\t |***** route_software           : %10d *****| \t", route_software)          };
    str = {str,  $sformatf("\n\t |***** type_bypass              : %10d *****| \t", type_bypass)             };
    str = {str,  $sformatf("\n\t |***** boot_bypass_disable      : %10d *****| \t", boot_bypass_disable)     };
    str = {str,  $sformatf("\n\t |------------ knobs ------------------------------| \t")                    };
    str = {str,  $sformatf("\n\t |***** enable_pct               : %10d *****| \t", enable_pct)              };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_read_pct    : %10d *****| \t", otp_en_es_fw_read_pct)   };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_over_pct    : %10d *****| \t", otp_en_es_fw_over_pct)   };
    str = {str,  $sformatf("\n\t |***** route_software_pct       : %10d *****| \t", route_software_pct)      };
    str = {str,  $sformatf("\n\t |***** type_bypass_pct          : %10d *****| \t", type_bypass_pct)         };
    str = {str,  $sformatf("\n\t |***** boot_bypass_disable_pct  : %10d *****| \t", boot_bypass_disable_pct) };
    str = {str,  $sformatf("\n\t |*************************************************| \t")                    };
    str = {str, "\n"};
    return str;
  endfunction

endclass
