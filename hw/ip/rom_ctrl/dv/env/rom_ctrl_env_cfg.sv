// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rom_ctrl_regs_reg_block));

  string rom_ral_name = "rom_ctrl_prim_reg_block";

  // ext component cfgs
  rand kmac_app_agent_cfg m_kmac_agent_cfg;

  // Memory backdoor util instance for ROM.
  mem_bkdr_util mem_bkdr_util_h;

  // ext interfaces
  rom_ctrl_vif rom_ctrl_vif;

  // Default is 10ms (see default_spinwait_timeout_ns in csr_utils_pkg.sv)
  // We have to increase this here since the ROM check may actually take longer than that,
  // which sometimes causes blocked TL accesses to time out.
  uint tl_access_timeout_ns = 40_000_000; // 40ms

  // A handle to the scoreboard, used to flag expected errors.
  rom_ctrl_scoreboard scoreboard;

  // Control the device-side delay for the kmac app agent that talks to the dut. If it is large,
  // rom_ctrl will spend all its time waiting for kmac to accept words that rom_ctrl is trying to
  // send to kmac. Randomise this to be small with high probability and occasionally make it 10 (to
  // check that the interface from rom_ctrl to kmac can be stalled properly).
  constraint kmac_accept_delay_max_c {
    if (!m_kmac_agent_cfg.m_data_push_agent_cfg.zero_delays) {
      m_kmac_agent_cfg.m_data_push_agent_cfg.device_delay_max dist { 1 :/ 10, 10 :/ 1 };
    }
  }

  `uvm_object_utils_begin(rom_ctrl_env_cfg)
  `uvm_object_utils_end

  function new (string name="");
    super.new(name);

    can_reset_with_csr_accesses = 1'b1;

    list_of_alerts = rom_ctrl_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal";
    ral_model_names.push_back("rom_ctrl_prim_reg_block");

    num_interrupts = 0;

    m_kmac_agent_cfg = kmac_app_agent_cfg::type_id::create("m_kmac_agent_cfg");
    m_kmac_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_kmac_agent_cfg.start_default_device_seq = 1'b1;
    m_kmac_agent_cfg.constant_share_means_error = 1'b0;
    // The checker reads the upper 8 words of ROM which takes 9 cycles. The rsp_delay_max has been
    // rounded off by 9*2=18 cycles along with adding 2 just to give an extra precision.
    m_kmac_agent_cfg.rsp_delay_min = 'd0;
    m_kmac_agent_cfg.rsp_delay_max = 'd20;

    sec_cm_alert_name = "fatal";
  endfunction

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);

    // default TLUL supports 1 outstanding item, the rom TLUL supports 2 outstanding items.
    m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 1;
    m_tl_agent_cfgs[rom_ral_name].max_outstanding_req = 2;

    // Tell the CIP base code what bit gets set if we see a TL fault.
    tl_intg_alert_fields[ral.fatal_alert_cause.integrity_error] = 1;
  endfunction

  // Override the default implementation in dv_base_env_cfg.
  //
  // This is required for the SRAM environment for reuse at the chip level as 2 different
  // parameterizations of the design and testbench exist, as a result the custom RAL model for the
  // SRAM memory primitive must also be explicitly parameterized.
  //
  // We cannot instantiate parameterized UVM objects/components using the standard factory
  // mechanisms, so a custom instantiation method is required here.
  //
  // Note that the SRAM only has 2 RAL models, one is the "default" CSR model,
  // and the other is the custom model to represent the memory primitive.
  virtual function dv_base_reg_block create_ral_by_name(string name);
    if (name == RAL_T::type_name) begin
      return super.create_ral_by_name(name);
    end else if (name == rom_ral_name) begin
      return rom_ctrl_prim_reg_block#(ROM_WORD_ADDR_WIDTH)::type_id::create(rom_ral_name);
    end else begin
      `uvm_error(`gfn, $sformatf("%0s is an illegal RAL model name", name))
    end
  endfunction

endclass
