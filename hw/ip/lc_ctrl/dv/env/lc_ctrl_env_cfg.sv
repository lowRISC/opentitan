// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(lc_ctrl_reg_block));

  // ext component cfgs
  push_pull_agent_cfg#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                       .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)) m_otp_prog_pull_agent_cfg;
  push_pull_agent_cfg#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)) m_otp_token_pull_agent_cfg;
  alert_esc_agent_cfg  m_esc_scrap_state1_agent_cfg;
  alert_esc_agent_cfg  m_esc_scrap_state0_agent_cfg;
  jtag_riscv_agent_cfg m_jtag_riscv_agent_cfg;
  uvm_reg_map          jtag_riscv_map;

  // ext interfaces
  pwr_lc_vif  pwr_lc_vif;
  lc_ctrl_vif lc_ctrl_vif;

  // Use JTAG for register accesses
  // TODO: use multiple address maps
  bit jtag_csr;

  `uvm_object_utils_begin(lc_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = lc_ctrl_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_bus_integ_error";
    super.initialize(csr_base_addr);

    m_otp_prog_pull_agent_cfg = push_pull_agent_cfg#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
        .DeviceDataWidth(OTP_PROG_DDATA_WIDTH))::type_id::create("m_otp_prog_pull_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_otp_prog_pull_agent_cfg)
    m_otp_prog_pull_agent_cfg.agent_type            = PullAgent;
    m_otp_prog_pull_agent_cfg.if_mode               = Device;
    m_otp_prog_pull_agent_cfg.in_bidirectional_mode = 1;

    m_otp_token_pull_agent_cfg = push_pull_agent_cfg#(
                                 .HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth))
        ::type_id::create("m_otp_token_pull_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_otp_token_pull_agent_cfg)
    m_otp_token_pull_agent_cfg.agent_type                 = PullAgent;
    m_otp_token_pull_agent_cfg.if_mode                    = Device;
    m_otp_token_pull_agent_cfg.in_bidirectional_mode      = 1;
    m_otp_token_pull_agent_cfg.hold_d_data_until_next_req = 1;

    m_esc_scrap_state1_agent_cfg = alert_esc_agent_cfg::type_id::create(
        "m_esc_scrap_state1_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_scrap_state1_agent_cfg)
    m_esc_scrap_state1_agent_cfg.is_alert = 0;

    m_esc_scrap_state0_agent_cfg = alert_esc_agent_cfg::type_id::create(
        "m_esc_scrap_state0_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_esc_scrap_state0_agent_cfg)
    m_esc_scrap_state0_agent_cfg.is_alert = 0;

    m_jtag_riscv_agent_cfg = jtag_riscv_agent_cfg::type_id::create("m_jtag_riscv_agent_cfg");
    `DV_CHECK_RANDOMIZE_FATAL(m_jtag_riscv_agent_cfg)

    jtag_csr = 0;

    // Set base address for JTAG map
    ral.set_base_addr(ral.default_map.get_base_addr(), jtag_riscv_map);
    //jtag_riscv_map.set_base_addr(csr_base_addr);

    ral.print();
  endfunction

  protected virtual function void apply_ral_fixes();
    uvm_reg_map clone;
    // Current block being built is saved to 'ral'
    jtag_riscv_map = clone_reg_map("jtag_riscv_map", ral.default_map);
  endfunction

  virtual function uvm_reg_map clone_reg_map(
        string name,
        uvm_reg_map map,
        uvm_reg_addr_t base_addr = 0,
        int n_bytes = 4,
        uvm_endianness_e endian = UVM_LITTLE_ENDIAN,
        bit byte_addressing = 1
        );
    uvm_reg_map clone;
    uvm_reg_map submaps[$];
    uvm_reg regs[$];
    uvm_reg_block blk;
    uvm_mem mems[$];

    map.get_submaps(submaps);
    if (submaps.size()) `uvm_fatal(`gfn, "clone_reg_map: submaps are not yet implemented");

    // Clone the map
    blk=map.get_parent();
    clone = blk.create_map(
      .name(name),
   		.base_addr(base_addr),
      .n_bytes(n_bytes),
   		.endian(endian),
   		.byte_addressing(byte_addressing)
      );

    // Clone the registers
    map.get_registers(regs, UVM_NO_HIER);
    while (regs.size()) begin
      uvm_reg rg;
      rg = regs.pop_front();
      clone.add_reg(
        .rg(rg),
        .offset(rg.get_offset(map)),
        .rights(rg.get_rights(map)),
        .unmapped(0),
        .frontdoor(null)
      );
    end

    // Clone the memories
    map.get_memories(mems, UVM_NO_HIER);
    while (mems.size()) begin
      uvm_mem mem;
      mem = mems.pop_front();
      clone.add_mem(
        .mem(mem),
        .offset(mem.get_offset(0, map)),
        .rights(mem.get_rights(map)),
        .unmapped(0),
        .frontdoor(null)
      );
    end
    return clone;
  endfunction

endclass
