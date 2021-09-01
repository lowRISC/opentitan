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
  uint   otp_en_cs_sw_app_read_pct, regwen_pct,
         enable_pct, sw_app_enable_pct, read_int_state_pct,
         chk_int_state_pct;

  rand bit                      chk_int_state, regwen;
  rand bit [3:0]                enable, sw_app_enable, read_int_state;
  rand otp_ctrl_pkg::otp_en_t   otp_en_cs_sw_app_read;

  // Variables
  bit                                    compliance[NUM_HW_APPS], status[NUM_HW_APPS];
  bit [csrng_env_pkg::KEY_LEN-1:0]       key[NUM_HW_APPS];
  bit [csrng_env_pkg::BLOCK_LEN-1:0]     v[NUM_HW_APPS];
  bit [csrng_env_pkg::RSD_CTR_LEN-1:0]   reseed_counter[NUM_HW_APPS];

  constraint c_otp_en_cs_sw_app_read {otp_en_cs_sw_app_read dist {
                                      otp_ctrl_pkg::Enabled  :/ otp_en_cs_sw_app_read_pct,
                                      otp_ctrl_pkg::Disabled :/ (100 - otp_en_cs_sw_app_read_pct) };}

  constraint c_regwen { regwen dist {
                        1 :/ regwen_pct,
                        0 :/ (100 - regwen_pct) };}

  constraint c_enable { enable dist {
                        csrng_pkg::CS_FIELD_ON  :/ enable_pct,
                        ~csrng_pkg::CS_FIELD_ON :/ (100 - enable_pct) };}

  constraint c_sw_app_enable { sw_app_enable dist {
                               csrng_pkg::CS_FIELD_ON  :/ sw_app_enable_pct,
                               ~csrng_pkg::CS_FIELD_ON :/ (100 - sw_app_enable_pct) };}

  constraint c_read_int_state { read_int_state dist {
                                csrng_pkg::CS_FIELD_ON  :/ read_int_state_pct,
                                ~csrng_pkg::CS_FIELD_ON :/ (100 - read_int_state_pct) };}

  constraint c_chk_int_state { chk_int_state dist {
                               1 :/ chk_int_state_pct,
                               0 :/ (100 - chk_int_state_pct) };}

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

  function void print_internal_state(bit [NUM_HW_APPS-1:0] hwapp);
    `uvm_info(`gfn, $sformatf("********** internal_state **********"), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.reseed_counter[%0d]       = %0d", hwapp,
         reseed_counter[hwapp]), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.compliance[%0d]/status[%0d] = 0b%0b", hwapp, hwapp,
         {compliance[hwapp], status[hwapp]}), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.key[%0d] = 0x%0h", hwapp, key[hwapp]), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.v[%0d]   = 0x%0h", hwapp, v[hwapp]), UVM_DEBUG)
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
    `uvm_info(`gfn, $sformatf("hw_reseed_counter[%0d]  = %0d",
        hwapp, hw_reseed_counter), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.reseed_counter[%0d] = %0d",
        hwapp, reseed_counter[hwapp]), UVM_DEBUG)
    `DV_CHECK_EQ_FATAL(hw_reseed_counter, reseed_counter[hwapp])
    for (int i = 0; i < BLOCK_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_v = (rdata<<TL_DW*i) + hw_v;
    end
    `uvm_info(`gfn, $sformatf("hw_v[%0d]  = 0x%0h",
        hwapp, hw_v), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.v[%0d] = 0x%0h",
        hwapp, v[hwapp]), UVM_DEBUG)
    `DV_CHECK_EQ_FATAL(hw_v, v[hwapp])
    for (int i = 0; i < KEY_LEN/TL_DW; i++) begin
      csr_rd(.ptr(ral.int_state_val), .value(rdata));
      hw_key = (rdata<<TL_DW*i) + hw_key;
    end
    `uvm_info(`gfn, $sformatf("hw_key[%0d]  = 0x%0h",
        hwapp, hw_key), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.key[%0d] = 0x%0h",
        hwapp, key[hwapp]), UVM_DEBUG)
    `DV_CHECK_EQ_FATAL(hw_key, key[hwapp])
    csr_rd(.ptr(ral.int_state_val), .value(rdata));
    hw_compliance = rdata[1];
    hw_status     = rdata[0];
    `uvm_info(`gfn, $sformatf("hw_compliance/status[%0d]  = 0b%b",
        hwapp, {hw_compliance, hw_status}), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("cfg.compliance/status[%0d] = 0b%b",
        hwapp, {compliance[hwapp], status[hwapp]}), UVM_DEBUG)
    `DV_CHECK_EQ_FATAL({hw_compliance, hw_status}, {compliance[hwapp], status[hwapp]})
 endtask

  virtual function string convert2string();
    string str = "";
    str = {str, "\n"};
    str = {str,  $sformatf("\n\t |************** csrng_env_cfg *****************| \t")                           };
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read     : 0x%4h *****| \t", otp_en_cs_sw_app_read)     };
    str = {str,  $sformatf("\n\t |***** enable                    : 0x%4h *****| \t", enable)                    };
    str = {str,  $sformatf("\n\t |***** sw_app_enable             : 0x%4h *****| \t", sw_app_enable)             };
    str = {str,  $sformatf("\n\t |***** read_int_state            : 0x%4h *****| \t", read_int_state)            };
    str = {str,  $sformatf("\n\t |***** regwen                    :   %4d *****| \t", regwen)                    };
    str = {str,  $sformatf("\n\t |***** chk_int_state             :   %4d *****| \t", chk_int_state)             };
    str = {str,  $sformatf("\n\t |-------------- knobs -------------------------| \t")                           };
    str = {str,  $sformatf("\n\t |***** otp_en_cs_sw_app_read_pct :   %4d *****| \t", otp_en_cs_sw_app_read_pct) };
    str = {str,  $sformatf("\n\t |***** regwen_pct                :   %4d *****| \t", regwen_pct)                };
    str = {str,  $sformatf("\n\t |***** enable_pct                :   %4d *****| \t", enable_pct)                };
    str = {str,  $sformatf("\n\t |***** sw_app_enable_pct         :   %4d *****| \t", sw_app_enable_pct)         };
    str = {str,  $sformatf("\n\t |***** read_int_state_pct        :   %4d *****| \t", read_int_state_pct)        };
    str = {str,  $sformatf("\n\t |***** chk_int_state_pct         :   %4d *****| \t", chk_int_state_pct)         };
    str = {str,  $sformatf("\n\t |**********************************************| \t")                           };
    str = {str, "\n"};
    return str;
  endfunction

endclass
