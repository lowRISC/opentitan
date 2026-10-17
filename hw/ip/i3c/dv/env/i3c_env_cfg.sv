// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i3c_env_cfg extends cip_base_env_cfg #(.RAL_T(i3c_reg_block));

  // Clock and reset of the AON domain, which holds the reset detector registers.
  virtual clk_rst_if clk_aon_rst_vif;

  // Pull-ups that model board-level resistors on the I3C bus (SDA, SCL).
  board_pullup_vif_t board_pullup_vif;

  // Pull-up and high-keeper enables that the DUT drives onto the I3C bus.
  bus_ctrl_vif_t bus_ctrl_vif;

  // Writes to the message buffer memory.
  virtual i3c_buf_mon_if buf_mon_vif;

  // Enable the board-level pull-ups on SDA and SCL.
  //
  // The DUT controls its own pull-ups and high-keepers on the bus. If a test disables all of them
  // whilst no device drives the bus (e.g. by writing random values to PHY_CONFIG), SDA and SCL
  // float, which is a software misconfiguration on real hardware. Tests that are not about I/O
  // correctness may enable these pull-ups to keep the bus at a defined level.
  bit en_board_pullup = 1'b0;

  `uvm_object_utils_begin(i3c_env_cfg)
    `uvm_field_int(en_board_pullup, UVM_DEFAULT)
  `uvm_object_utils_end

  // The DUT runs at the clock frequency that it is configured for.
  constraint clk_freq_mhz_i3c_c {
    clk_freq_mhz == ClkFreqMhz;
  }

  `uvm_object_new

  virtual function void initialize(bit inherit_ral_models = 1'b0);
    list_of_alerts = i3c_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_fault";
    super.initialize(inherit_ral_models);

    void'($value$plusargs("en_board_pullup=%0b", en_board_pullup));

    num_interrupts = ral.intr_state.get_n_used_bits();
    `DV_CHECK_EQ_FATAL(num_interrupts, NumI3cIntr)
  endfunction

  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
    i3c_reg_block i3c_ral;
    super.post_build_ral_settings(ral);
    `downcast(i3c_ral, ral)
    set_absent_targ_resets(i3c_ral);
    set_num_targets_reset(i3c_ral);
    add_queue_port_access_excls(i3c_ral);
    narrow_pin_level_excls(i3c_ral);
    set_mem_walk_excls(i3c_ral);
  endfunction

  // Narrow the exclusions of the registers that reflect the SCL and SDA pin levels.
  //
  // i3c.hjson excludes PRESENT_STATE_DEBUG and TARG_STATE_DEBUG from all CSR checks, because the
  // chip-level simulation does not drive the pins. In this testbench the bus model holds the pins
  // at defined levels, so the reset values of these registers are deterministic. Replace the
  // register exclusions with field exclusions that only apply to the non-init tests.
  protected virtual function void narrow_pin_level_excls(i3c_reg_block i3c_ral);
    csr_excl_item csr_excl = i3c_ral.get_excl_item();
    dv_base_reg   regs[$]  = '{i3c_ral.present_state_debug, i3c_ral.targ_state_debug};
    foreach (regs[i]) begin
      dv_base_reg_field flds[$];
      csr_excl.enable_excl(regs[i].get_full_name(), 1'b0);
      regs[i].get_dv_base_reg_fields(flds);
      foreach (flds[f]) csr_excl.add_excl(flds[f].get_full_name(), CsrExclCheck, CsrNonInitTests);
    end
  endfunction

  // Exclude memory windows from the generic memory walk (`uvm_mem_walk_seq`).
  //
  // - HCI_PORTS and TTI_PORTS are queue ports, not storage: a read returns a queue entry rather
  //   than the data written to the same address.
  // - The DAT and the DCT do not store the reserved fields of their entries, which read as zero.
  //   `i3c_csr_mem_walk_seq` walks them with a mask of the stored bits instead.
  protected virtual function void set_mem_walk_excls(i3c_reg_block i3c_ral);
    uvm_mem mems[$] = '{i3c_ral.hci_ports, i3c_ral.tti_ports, i3c_ral.dat, i3c_ral.dct};
    foreach (mems[i]) begin
      uvm_resource_db#(bit)::set({"REG::", mems[i].get_full_name()}, "NO_MEM_WALK_TEST", 1);
    end
  endfunction

  // Exclude the register fields that accesses to the HCI and TTI queue ports change.
  //
  // csr_mem_rw_with_rand_reset accesses the memory windows, including the queue ports, whilst it
  // runs csr_rw. No other CSR test accesses the queue ports, so these exclusions only apply to this
  // test:
  // - A read from an empty queue or a write to a full queue sets the HCIQ_ERR or TTIQ_ERR bit of
  //   BUFFER_STATUS.
  // - A Tx or IBI descriptor in the TTI queues lets the hardware set SUSPENDED or IBI_SUSPENDED in
  //   TARG_PIO_CONTROL, and while those are set, writes to TARG_PIO_CONTROL can make the hardware
  //   clear ABORT or IBI_ABORT.
  protected virtual function void add_queue_port_access_excls(i3c_reg_block i3c_ral);
    csr_excl_item     csr_excl = i3c_ral.get_excl_item();
    dv_base_reg_field flds[$] = '{i3c_ral.buffer_status.hciq_err,
                                  i3c_ral.buffer_status.ttiq_err,
                                  i3c_ral.targ_pio_control.suspended,
                                  i3c_ral.targ_pio_control.ibi_suspended,
                                  i3c_ral.targ_pio_control.abort,
                                  i3c_ral.targ_pio_control.ibi_abort};
    if (!$test$plusargs("run_csr_mem_rw_with_rand_reset")) return;
    foreach (flds[i]) csr_excl.add_excl(flds[i].get_full_name(), CsrExclCheck, CsrRwTest);
  endfunction

  // Align the RAL with the Virtual Targets that the DUT does not implement.
  //
  // The CSRs describe the Tx buffer and Tx descriptor queue state and free levels of all
  // `MaxTargets` Virtual Targets, and their reset values derive from the default apportioning of
  // the message buffer. `i3c_core` ties the register view of that state off for the Virtual
  // Targets that the DUT does not implement (`gen_no_targ_tx`), so they read as zero. This matches
  // `chip_env_cfg::set_i3c_absent_targ_resets()`.
  protected virtual function void set_absent_targ_resets(i3c_reg_block i3c_ral);
    string state_regs[$] = {"targ_txbuf_state", "targ_txdesc_state", "targ_tx_queue_status_level"};
    `DV_CHECK_LE_FATAL(NumTargets, MaxTargets)
    foreach (state_regs[i]) begin
      for (uint t = NumTargets; t < MaxTargets; t++) begin
        string        reg_name = $sformatf("%0s_%0d", state_regs[i], t);
        uvm_reg       rg       = i3c_ral.get_reg_by_name(reg_name);
        uvm_reg_field flds[$];
        `DV_CHECK_FATAL(rg != null, $sformatf("No register %0s", reg_name))
        rg.get_fields(flds);
        foreach (flds[f]) flds[f].set_reset(0);
      end
    end
  endfunction

  // `TARG_STATUS.NUM_TARGETS` reports the `NumTargets` parameter of the DUT.
  protected virtual function void set_num_targets_reset(i3c_reg_block i3c_ral);
    i3c_ral.targ_status.num_targets.set_reset(NumTargets);
  endfunction

endclass
