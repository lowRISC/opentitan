// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rom_ctrl_regs_reg_block));

  // ext component cfgs
  kmac_app_agent_cfg m_kmac_agent_cfg;

  // Memory backdoor util instance for ROM.
  mem_bkdr_util mem_bkdr_util_h;

  // ext interfaces
  rom_ctrl_vif rom_ctrl_vif;

  // Enables/disable all protocol delays.
  rand bit zero_delays;

  // Default is 10ms (see default_spinwait_timeout_ns in csr_utils_pkg.sv)
  // We have to increase this here since the ROM check may actually take longer than that,
  // which sometimes causes blocked TL accesses to time out.
  uint tl_access_timeout_ns = 40_000_000; // 40ms

  // Bias randomization in favor of enabling zero delays less often.
  constraint zero_delays_c {
    zero_delays dist { 0 := 8,
                       1 := 2 };
  }

  // Device-side delay for both push/pull protocols.
  rand int unsigned device_delay_max;

  // A handle to the scoreboard, used to flag expected errors.
  rom_ctrl_scoreboard scoreboard;

  constraint device_delay_max_c {
    solve zero_delays before device_delay_max;
    if (zero_delays) {
      device_delay_max == 0;
    } else {
      device_delay_max dist {
        [1:20] :/ 2,
        [21:50] :/ 4
      };
    }
  }

  `uvm_object_utils_begin(rom_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rom_ctrl_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal";

    ral_model_names.push_back("rom_ctrl_rom_reg_block");

    super.initialize(csr_base_addr);
    num_interrupts = 0;

    m_kmac_agent_cfg = kmac_app_agent_cfg::type_id::create("m_kmac_agent_cfg");
    m_kmac_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_kmac_agent_cfg.start_default_device_seq = 1'b1;
    m_kmac_agent_cfg.constant_share_means_error = 1'b0;

    m_tl_agent_cfgs["rom_ctrl_rom_reg_block"].max_outstanding_req = 2;
    m_tl_agent_cfgs["rom_ctrl_regs_reg_block"].max_outstanding_req = 1;

    // Tell the CIP base code what bit gets set if we see a TL fault.
    tl_intg_alert_fields[ral.fatal_alert_cause.integrity_error] = 1;
    sec_cm_alert_name = "fatal";
  endfunction

endclass
