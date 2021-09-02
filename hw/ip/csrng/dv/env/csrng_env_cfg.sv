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

  rand csrng_agent_cfg   m_edn_agent_cfg[NUM_HW_APPS];

  virtual pins_if#(8)   otp_en_cs_sw_app_read_vif;

  // Knobs & Weights
  uint             enable_pct, sw_app_enable_pct, otp_en_cs_sw_app_read_pct,
                   cmd_length_0_pct, cmd_flags_0_pct, chk_int_state_pct;
  rand bit         chk_int_state;
  rand bit [3:0]   enable, sw_app_enable, cmd_length, cmd_flags;
  rand otp_ctrl_pkg::otp_en_t   otp_en_cs_sw_app_read;

  // Variables
  bit                                    compliance[NUM_HW_APPS], status[NUM_HW_APPS];
  bit [csrng_env_pkg::KEY_LEN-1:0]       key[NUM_HW_APPS];
  bit [csrng_env_pkg::BLOCK_LEN-1:0]     v[NUM_HW_APPS];
  bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   reseed_counter[NUM_HW_APPS];

  // Constraints
  constraint c_enable {enable dist {
                       csrng_pkg::CS_FIELD_ON         :/ enable_pct,
                       [0:csrng_pkg::CS_FIELD_ON - 1] :/ (100 - enable_pct)/2,
                       [csrng_pkg::CS_FIELD_ON + 1:$] :/ (100 - enable_pct)/2 };}

  constraint c_sw_app_enable {sw_app_enable dist {
                              csrng_pkg::CS_FIELD_ON         :/ sw_app_enable_pct,
                              [0:csrng_pkg::CS_FIELD_ON - 1] :/ (100 - sw_app_enable_pct)/2,
                              [csrng_pkg::CS_FIELD_ON + 1:$] :/ (100 - sw_app_enable_pct)/2 };}

  constraint c_otp_en_cs_sw_app_read {otp_en_cs_sw_app_read dist {
                                      otp_ctrl_pkg::Enabled  :/ otp_en_cs_sw_app_read_pct,
                                      otp_ctrl_pkg::Disabled :/ (100 - otp_en_cs_sw_app_read_pct) };}

  constraint c_chk_int_state {chk_int_state dist {
                              1 :/ chk_int_state_pct,
                              0 :/ (100 - chk_int_state_pct)};}

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = csrng_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_alert";
    super.initialize(csr_base_addr);

    // create agent configs
    m_entropy_src_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::
                              FIPS_CSRNG_BUS_WIDTH))::type_id::create("m_entropy_src_agent_cfg");

    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_agent_cfg[i] = csrng_agent_cfg::type_id::create($sformatf("m_edn_agent_cfg[%0d]", i));
    end

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

    // Compare internal state
  task check_int_state(uint hwapp);
    bit [TL_DW-1:0]                        rdata;
    bit                                    hw_compliance, hw_status;
    bit [csrng_env_pkg::KEY_LEN-1:0]       hw_key;
    bit [csrng_env_pkg::BLOCK_LEN-1:0]     hw_v;
    bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   hw_reseed_counter;

    csr_wr(.ptr(ral.int_state_num), .value(hwapp));
    csr_rd_check(.ptr(ral.int_state_num), .compare_vs_ral(1'b1));
    for (int i = 0; i < RSD_CTR_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_reseed_counter = (rdata<<TL_DW*i) + hw_reseed_counter;
    end
    `DV_CHECK_EQ_FATAL(hw_reseed_counter, reseed_counter[hwapp])
    for (int i = 0; i < BLOCK_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_v = (rdata<<TL_DW*i) + hw_v;
    end
    `DV_CHECK_EQ_FATAL(hw_v, v[hwapp])
    for (int i = 0; i < KEY_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_key = (rdata<<TL_DW*i) + hw_key;
    end
    `DV_CHECK_EQ_FATAL(hw_key, key[hwapp])
    csr_rd(.ptr(ral.int_state_val), .value(rdata));
    hw_compliance = rdata[1];
    hw_status     = rdata[0];
    `DV_CHECK_EQ_FATAL({hw_compliance, hw_status}, {compliance[hwapp], status[hwapp]})
 endtask

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |********** csrng_env_cfg ***********************| \t")                        };
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read     : %10d *****| \t", otp_en_cs_sw_app_read)       };
    str = {str,  $sformatf("\n\t |***** enable                    : %10h *****| \t", enable)                      };
    str = {str,  $sformatf("\n\t |***** sw_app_enable             : %10h *****| \t", sw_app_enable)               };
    str = {str,  $sformatf("\n\t |***** chk_int_state             : %10d *****| \t", chk_int_state)               };
    str = {str,  $sformatf("\n\t |***** cmd_length                : %10d *****| \t", cmd_length)                  };
    str = {str,  $sformatf("\n\t |***** cmd_flags                 : %10d *****| \t", cmd_flags)                   };
    str = {str,  $sformatf("\n\t |---------- knobs -------------------------------| \t")                        };
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read_pct : %10d *****| \t", otp_en_cs_sw_app_read_pct) };
    str = {str,  $sformatf("\n\t |***** enable_pct                : %10d *****| \t", enable_pct)                };
    str = {str,  $sformatf("\n\t |***** sw_app_enable_pct         : %10d *****| \t", sw_app_enable_pct)         };
    str = {str,  $sformatf("\n\t |***** chk_int_state_pct         : %10d *****| \t", chk_int_state_pct)         };
    str = {str,  $sformatf("\n\t |***** cmd_length_0_pct          : %10d *****| \t", cmd_length_0_pct)          };
    str = {str,  $sformatf("\n\t |***** cmd_flags_0_pct           : %10d *****| \t", cmd_flags_0_pct)           };
    str = {str,  $sformatf("\n\t |************************************************| \t")                        };
    str = {str, "\n"};
    return str;
  endfunction

endclass
