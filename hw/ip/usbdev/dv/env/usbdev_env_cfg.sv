// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_env_cfg extends cip_base_env_cfg #(.RAL_T(usbdev_reg_block));

  virtual clk_rst_if  usb_clk_rst_vif;
  rand clk_freq_mhz_e usb_clk_freq_mhz;

  // Reset kinds for USB
  string reset_kinds[] = {"HARD", "TL_IF", "USB_IF"};

  // Constrain USB to be at 48MHz based on spec
  constraint usb_clk_freq_mhz_c {
    usb_clk_freq_mhz == dv_utils_pkg::ClkFreq48Mhz;
  }

  // ext component cfgs
  rand usb20_agent_cfg m_usb20_agent_cfg;

  `uvm_object_utils_begin(usbdev_env_cfg)
    `uvm_field_object(m_usb20_agent_cfg,                UVM_DEFAULT)
    `uvm_field_enum  (clk_freq_mhz_e, usb_clk_freq_mhz, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // create usb20 agent config obj
    m_usb20_agent_cfg = usb20_agent_cfg::type_id::create("m_usb20_agent_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

  // ral flow is limited in terms of setting correct field access policies and reset values
  // We apply those fixes here - please note these fixes need to be reflected in the scoreboard
  protected virtual function void apply_ral_fixes();
    // fix access policies
    // Out of reset, the link is in disconnected state.
    ral.intr_state.disconnected.set_reset(1'b1);
  endfunction

endclass
