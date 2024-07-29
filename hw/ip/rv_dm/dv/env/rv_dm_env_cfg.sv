// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env_cfg extends cip_base_env_cfg #(.RAL_T(rv_dm_regs_reg_block));

  // ext component cfgs
  virtual rv_dm_if    rv_dm_vif;
  rand jtag_agent_cfg m_jtag_agent_cfg;
  rand tl_agent_cfg   m_tl_sba_agent_cfg;

  // This controls whether the scoreboard (if enabled) should check correctness of TL error
  // responses. It defaults to being true but a vseq that is forcing internal signals might need to
  // turn it off.
  bit tl_err_prediction = 1'b1;

  // This controls whether the scoreboard (if enabled) should check that we only see SBA responses
  // when debug is enabled. It defaults to being true but a vseq that is forcing internal signals
  // might need to turn it off.
  bit sba_tl_tx_requires_debug = 1'b1;

  // A handle to a clock interface for the LC domain. We don't actually use the clock itself, but
  // use the unsynchronised reset signal.
  virtual clk_rst_if clk_lc_rst_vif;

  // The JTAG DMI register model.
  rand jtag_dmi_reg_block jtag_dmi_ral;

  // The JTAG RV debugger model.
  jtag_rv_debugger debugger;

  // A constant that can be referenced from anywhere.
  string mem_ral_name = "rv_dm_mem_reg_block";

  `uvm_object_utils_begin(rv_dm_env_cfg)
    `uvm_field_object(m_jtag_agent_cfg,   UVM_DEFAULT)
    `uvm_field_object(m_tl_sba_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(jtag_dmi_ral,       UVM_DEFAULT)
    `uvm_field_object(debugger,           UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rv_dm_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_fault";

    // Set up second RAL model for debug memory and associated collateral
    ral_model_names.push_back(mem_ral_name);

    // both RAL models use same clock frequency
    clk_freqs_mhz["rv_dm_mem_reg_block"] = clk_freq_mhz;

    super.initialize(csr_base_addr);
    `uvm_info(`gfn, $sformatf("ral_model_names: %0p", ral_model_names), UVM_LOW)

    // Both, the regs and the debug mem TL device (in the DUT) only support 1 outstanding.
    m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 1;
    m_tl_agent_cfgs[mem_ral_name].max_outstanding_req = 1;

    // Create jtag agent config obj
    m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
    m_jtag_agent_cfg.if_mode = dv_utils_pkg::Host;
    m_jtag_agent_cfg.is_active = 1'b1;
    m_jtag_agent_cfg.ir_len = JTAG_IR_LEN;

    // Set the 'correct' IDCODE register value to the JTAG DTM RAL.
    m_jtag_agent_cfg.jtag_dtm_ral.idcode.set_reset(RV_DM_JTAG_IDCODE);

    // Create TL agent config obj for the SBA port.
    m_tl_sba_agent_cfg = tl_agent_cfg::type_id::create("m_tl_sba_agent_cfg");
    m_tl_sba_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_tl_sba_agent_cfg.is_active = 1'b1;
    m_tl_sba_agent_cfg.max_outstanding_req = 1;

    jtag_dmi_ral = create_jtag_dmi_reg_block(m_jtag_agent_cfg);
    // Fix the reset values of these fields based on our design.
    `uvm_info(`gfn, "Fixing reset values in jtag_dmi_ral", UVM_LOW)
    jtag_dmi_ral.hartinfo.dataaddr.set_reset(dm::DataAddr);
    jtag_dmi_ral.hartinfo.datasize.set_reset(dm::DataCount);
    jtag_dmi_ral.hartinfo.dataaccess.set_reset(1);
    jtag_dmi_ral.hartinfo.nscratch.set_reset(2);
    jtag_dmi_ral.abstractcs.datacount.set_reset(dm::DataCount);
    jtag_dmi_ral.abstractcs.progbufsize.set_reset(dm::ProgBufSize);
    jtag_dmi_ral.dmstatus.authenticated.set_reset(1);  // No authentication performed.
    jtag_dmi_ral.sbcs.sbaccess32.set_reset(1);
    jtag_dmi_ral.sbcs.sbaccess16.set_reset(1);
    jtag_dmi_ral.sbcs.sbaccess8.set_reset(1);
    jtag_dmi_ral.sbcs.sbasize.set_reset(32);
    apply_jtag_dmi_ral_csr_excl();

    // Create the JTAG RV debugger instance.
    debugger = jtag_rv_debugger::type_id::create("debugger");
    debugger.set_cfg(m_jtag_agent_cfg);
    debugger.set_ral(jtag_dmi_ral);
    debugger.num_harts = NUM_HARTS;
  endfunction

  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
    // The backdoor HDL paths are set incorrectly on the debug mem RAL structures by the reggen
    // tool. We just remove all HDL paths and skip backdoor writes entirely.
    // TODO: Enable backdoor writes later.
    if (ral.get_name() == mem_ral_name) begin
      uvm_reg regs[$];

      ral.get_registers(regs);
      foreach (regs[i]) begin
        regs[i].clear_hdl_path("ALL");
      end
    end
  endfunction

  // Apply RAL exclusions externally since the RAL itself is considered generic. The IP it is used
  // in constrains the RAL with its implementation details.
  virtual function void apply_jtag_dmi_ral_csr_excl();
    csr_excl_item csr_excl = jtag_dmi_ral.get_excl_item();

    // We leave the DM 'activated' for CSR tests to reduce noise. We exclude this from further
    // writes to avoid side-effects.
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.dmactive.get_full_name(),
        CsrExclWrite, CsrNonInitTests);

    // This field is tied off to 0 due to no hart array mask being implemented.
    // TODO: Change these to access policy.
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hasel.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hartreset.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // Selecting a different hart in the middle of random read/writes impact other registers.
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hartsello.get_full_name(),
        CsrExclWrite, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.dmcontrol.hartselhi.get_full_name(),
        CsrExclWrite, CsrNonInitTests);

    // Writes to other CSRs may affect dmstatus, even the HW reset test.
    csr_excl.add_excl(jtag_dmi_ral.dmstatus.get_full_name(), CsrExclCheck, CsrAllTests);

    // We have only upto dm::DataCount number of these registers available.
    foreach (jtag_dmi_ral.abstractdata[i]) begin
      if (i >= dm::DataCount) begin
        csr_excl.add_excl(jtag_dmi_ral.abstractdata[i].get_full_name(),
            CsrExclWriteCheck, CsrNonInitTests);
      end
    end

    // We have only upto dm::ProgBufSize number of these registers available.
    foreach (jtag_dmi_ral.progbuf[i]) begin
      if (i >= dm::ProgBufSize) begin
        csr_excl.add_excl(jtag_dmi_ral.progbuf[i].get_full_name(),
            CsrExclWriteCheck, CsrNonInitTests);
      end
    end

    // These prevent an SBA access from being triggered, which have other side effects.
    csr_excl.add_excl(jtag_dmi_ral.sbcs.sbreadondata.get_full_name(),
        CsrExclWrite, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbcs.sbreadonaddr.get_full_name(),
        CsrExclWrite, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbdata0.get_full_name(),
        CsrExclWrite, CsrNonInitTests);

    // TODO: This should be an access policy change.
    csr_excl.add_excl(jtag_dmi_ral.sbcs.sbaccess.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // These SBA registers are not implemented, or unsupported due to 32-bit system.
    csr_excl.add_excl(jtag_dmi_ral.sbaddress1.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbaddress2.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbaddress3.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbdata2.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
    csr_excl.add_excl(jtag_dmi_ral.sbdata3.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // Abstractcs cmderr bits are updated by RTL.
    csr_excl.add_excl(jtag_dmi_ral.abstractcs.cmderr.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);

    // Not all bits of abstractauto are set - and its also impacted by writes to other CSRs.
    csr_excl.add_excl(jtag_dmi_ral.abstractauto.get_full_name(),
        CsrExclWriteCheck, CsrNonInitTests);
  endfunction

endclass
