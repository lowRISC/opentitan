// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_env_cfg extends cip_base_env_cfg #(.RAL_T(usbdev_reg_block));

  // Clock/reset for usbdev_aon_wake module.
  virtual clk_rst_if aon_clk_rst_vif;
  // Clock/reset for usbdpi host model (not usb20_agent).
  virtual clk_rst_if host_clk_rst_vif;
  // USB connection to usbdpi host model.
  virtual usb20_if   usb20_usbdpi_vif;
  // Timing reference for oscillator tuning.
  virtual usbdev_osc_tuning_if osc_tuning_vif;

  // Reset kinds for USB
  string reset_kinds[] = {"HARD", "TL_IF"};

  // Constrain the main clock to be at 48MHz based on spec
  rand uint usb_clk_freq_khz;
  constraint usb_clk_freq_khz_c {
    usb_clk_freq_khz == 48_000;
  }

  // Constrain the AON clock to be slower than the USB clock. For the usbdev_aon_wake logic
  // to operate correctly and not generate spurious reports of bus resets when detecting Low Speed
  // signaling, it requires a clock frequency lower than 1MHz cf the usbdev clock at 48MHz, so the
  // ratio should exceed 48. This is because 2 bit intervals @ 1.5Mbps may be seen - in the limit -
  // as being high for 3 clock edges at frequencies above 1MHz.
  //
  // In a real device we expect it to be as low as 200kHz.
  rand uint aon_clk_freq_khz;
  constraint aon_clk_freq_khz_c {
    aon_clk_freq_khz >  usb_clk_freq_khz / 300 &&
    aon_clk_freq_khz <= usb_clk_freq_khz / 48;
  }

  // Constrain the host clock to be close to that of the DUT at present; in time we shall want
  // to exercise a greater disparity and implement oscillator tuning for the DUT to track the
  // host.
  // For now we must ensure that the disparity cannot induce sampling errors over the maximum
  // length of a packet, with maximal initial phase shift. ie. less than one sampling interval
  // (at 48MHz) of drift over 4 x (16 + ((64x8) + 16)x7/6 + 2) bit intervals).
  rand uint host_clk_freq_khz;
  constraint host_clk_freq_khz_c {
    host_clk_freq_khz >= usb_clk_freq_khz - 18 &&
    host_clk_freq_khz <= usb_clk_freq_khz + 18;
  }

  // ext component cfgs
  rand usb20_agent_cfg m_usb20_agent_cfg;

  `uvm_object_utils_begin(usbdev_env_cfg)
    `uvm_field_object(m_usb20_agent_cfg,  UVM_DEFAULT)
    `uvm_field_int   (usb_clk_freq_khz,   UVM_DEFAULT)
    `uvm_field_int   (aon_clk_freq_khz,   UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = usbdev_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // create usb20 agent config obj
    m_usb20_agent_cfg = usb20_agent_cfg::type_id::create("m_usb20_agent_cfg");

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();
  endfunction

  // ral flow is limited in terms of setting correct field access policies and reset values
  // We apply those fixes here - please note these fixes need to be reflected in the scoreboard
  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
    usbdev_reg_block usbdev_ral;
    if (!$cast(usbdev_ral, ral)) return;
    // fix access policies
    // Out of reset, the link is in disconnected state.
    usbdev_ral.intr_state.disconnected.set_reset(1'b1);
  endfunction

endclass
