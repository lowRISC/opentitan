// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env_cfg extends cip_base_env_cfg #(.RAL_T(entropy_src_reg_block));

  import entropy_src_pkg::*;

  `uvm_object_utils_begin(entropy_src_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  // Ext component cfgs
  rand push_pull_agent_cfg#(.HostDataWidth(RNG_BUS_WIDTH))
       m_rng_agent_cfg;
  rand push_pull_agent_cfg#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))
       m_csrng_agent_cfg;

  virtual pins_if#(8)   otp_en_es_fw_read_vif;
  virtual pins_if#(8)   otp_en_es_fw_over_vif;

  // Knobs & Weights
  uint          enable_pct, route_software_pct, regwen_pct,
                otp_en_es_fw_read_pct, otp_en_es_fw_over_pct,
                type_bypass_pct, boot_bypass_disable_pct,
                entropy_data_reg_enable_pct, rng_bit_enable_pct;

  rand bit         regwen;
  rand bit [1:0]   rng_bit_sel;

  rand prim_mubi_pkg::mubi4_t   enable, route_software, type_bypass,
                                boot_bypass_disable, entropy_data_reg_enable,
                                rng_bit_enable;

  // TODO: randomize
  uint fips_window_size, bypass_window_size, boot_mode_retry_limit;
  int  seed_cnt;

  rand prim_mubi_pkg::mubi8_t   otp_en_es_fw_read, otp_en_es_fw_over;

  // Constraints
  constraint c_regwen {regwen dist {
      1 :/ regwen_pct,
      0 :/ (100 - regwen_pct) };}

  constraint c_otp_en_es_fw_read {otp_en_es_fw_read dist {
      prim_mubi_pkg::MuBi8True  :/ otp_en_es_fw_read_pct,
      prim_mubi_pkg::MuBi8False :/ (100 - otp_en_es_fw_read_pct) };}

  constraint c_otp_en_es_fw_over {otp_en_es_fw_over dist {
      prim_mubi_pkg::MuBi8True  :/ otp_en_es_fw_over_pct,
      prim_mubi_pkg::MuBi8False :/ (100 - otp_en_es_fw_over_pct) };}

  constraint c_enable {enable dist {
      prim_mubi_pkg::MuBi4True  :/ enable_pct,
      prim_mubi_pkg::MuBi4False :/ 100 - enable_pct };}

  constraint c_route {route_software dist {
      prim_mubi_pkg::MuBi4True  :/ route_software_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - route_software_pct) };}

  constraint c_bypass {type_bypass dist {
      prim_mubi_pkg::MuBi4True  :/ type_bypass_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - type_bypass_pct) };}

  constraint c_boot_bypass_disable {boot_bypass_disable dist {
      prim_mubi_pkg::MuBi4True  :/ boot_bypass_disable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - boot_bypass_disable_pct)};}

  constraint c_entropy_data_reg_enable {entropy_data_reg_enable dist {
      prim_mubi_pkg::MuBi4True  :/ entropy_data_reg_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - entropy_data_reg_enable_pct)};}

  constraint c_rng_bit_enable {rng_bit_enable dist {
      prim_mubi_pkg::MuBi4True  :/ rng_bit_enable_pct,
      prim_mubi_pkg::MuBi4False :/ (100 - rng_bit_enable_pct)};}

  // Functions
  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = entropy_src_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create agent config objs
    m_rng_agent_cfg   = push_pull_agent_cfg#(.HostDataWidth(RNG_BUS_WIDTH))::
                        type_id::create("m_rng_agent_cfg");
    m_csrng_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))::
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
    str = {str,  $sformatf("\n\t |**************** entropy_src_env_cfg *****************| \t")                         };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_read           : %12s *****| \t", otp_en_es_fw_read.name())       };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_over           : %12s *****| \t", otp_en_es_fw_over.name())       };
    str = {str,  $sformatf("\n\t |***** enable                      : %12s *****| \t", enable.name())                  };
    str = {str,  $sformatf("\n\t |***** route_software              : %12s *****| \t", route_software.name())          };
    str = {str,  $sformatf("\n\t |***** type_bypass                 : %12s *****| \t", type_bypass.name())             };
    str = {str,  $sformatf("\n\t |***** entropy_data_reg_enable     : %12s *****| \t", entropy_data_reg_enable.name()) };
    str = {str,  $sformatf("\n\t |***** boot_bypass_disable         : %12s *****| \t", boot_bypass_disable.name())     };
    str = {str,  $sformatf("\n\t |***** rng_bit_enable              : %12s *****| \t", rng_bit_enable.name())          };
    str = {str,  $sformatf("\n\t |***** rng_bit_sel                 : %12d *****| \t", rng_bit_sel)                    };
    str = {str,  $sformatf("\n\t |----------------- knobs ------------------------------| \t")                         };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_read_pct       : %12d *****| \t", otp_en_es_fw_read_pct)          };
    str = {str,  $sformatf("\n\t |***** otp_en_es_fw_over_pct       : %12d *****| \t", otp_en_es_fw_over_pct)          };
    str = {str,  $sformatf("\n\t |***** enable_pct                  : %12d *****| \t", enable_pct)                     };
    str = {str,  $sformatf("\n\t |***** route_software_pct          : %12d *****| \t", route_software_pct)             };
    str = {str,  $sformatf("\n\t |***** type_bypass_pct             : %12d *****| \t", type_bypass_pct)                };
    str = {str,  $sformatf("\n\t |***** entropy_data_reg_enable_pct : %12d *****| \t", entropy_data_reg_enable_pct)    };
    str = {str,  $sformatf("\n\t |***** boot_bypass_disable_pct     : %12d *****| \t", boot_bypass_disable_pct)        };
    str = {str,  $sformatf("\n\t |***** rng_bit_enable_pct          : %12d *****| \t", rng_bit_enable_pct)             };
    str = {str,  $sformatf("\n\t |******************************************************| \t")                         };
    str = {str, "\n"};
    return str;
  endfunction

endclass
