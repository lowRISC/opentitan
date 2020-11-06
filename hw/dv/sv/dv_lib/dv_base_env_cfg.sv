// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_env_cfg #(type RAL_T = dv_base_reg_block) extends uvm_object;

  bit is_active         = 1;
  bit en_scb            = 1; // can be changed at run-time
  bit en_scb_tl_err_chk = 1;
  bit en_scb_mem_chk    = 1;
  bit en_cov            = 1;
  bit has_ral           = 1;
  bit under_reset       = 0;

  // bit to configure all uvcs with zero delays to create high bw test
  rand bit zero_delays;

  // set zero_delays 40% of the time
  constraint zero_delays_c {
    zero_delays dist {1'b0 := 6, 1'b1 := 4};
  }

  // reg model & q of valid csr addresses
  RAL_T                             ral;
  dv_base_reg_block                 ral_models[$];
  bit [bus_params_pkg::BUS_AW-1:0]  csr_addrs[$];
  addr_range_t                      mem_ranges[$];

  // clk_rst_if & freq
  virtual clk_rst_if  clk_rst_vif;
  rand clk_freq_mhz_e clk_freq_mhz;

  `uvm_object_param_utils_begin(dv_base_env_cfg #(RAL_T))
    `uvm_field_int   (is_active,                    UVM_DEFAULT)
    `uvm_field_int   (en_scb,                       UVM_DEFAULT)
    `uvm_field_int   (en_cov,                       UVM_DEFAULT)
    `uvm_field_int   (zero_delays,                  UVM_DEFAULT)
    `uvm_field_enum  (clk_freq_mhz_e, clk_freq_mhz, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [bus_params_pkg::BUS_AW-1:0] csr_base_addr = '1);
    // build the ral model
    if (has_ral) begin
      uvm_reg_addr_t base_addr;

      ral = RAL_T::type_id::create("ral");

      // Build the register block with an arbitrary base address (we choose 0). We'll change it
      // later.
      ral.build(.base_addr(0), .csr_excl(null));
      apply_ral_fixes();
      ral.lock_model();

      // Now the model is locked, we know its layout. Set the base address for the register block.
      // The function internally picks a random one if we pass '1 to it, and performs an integrity
      // check on the set address.
      ral.set_base_addr(csr_base_addr);

      // Get list of valid csr addresses (useful in seq to randomize addr as well as in scb checks)
      get_csr_addrs(ral, csr_addrs);
      get_mem_addr_ranges(ral, mem_ranges);
      ral_models.push_back(ral);
    end
  endfunction

  // ral flow is limited in terms of setting correct field access policies and reset values
  // We apply those fixes here - please note these fixes need to be reflected in the scoreboard
  protected virtual function void apply_ral_fixes();
    // fix access policies & reset values
  endfunction

  virtual function void reset_asserted();
    this.under_reset = 1;
    csr_utils_pkg::reset_asserted();
  endfunction

  virtual function void reset_deasserted();
    this.under_reset = 0;
    csr_utils_pkg::reset_deasserted();
  endfunction

endclass
