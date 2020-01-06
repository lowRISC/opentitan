// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_env_cfg #(type RAL_T = dv_base_reg_block) extends uvm_object;

  bit                   is_active    = 1;
  bit                   en_scb       = 1; // can be changed at run-time
  bit                   en_cov       = 1;
  bit                   has_ral      = 1;
  bit                   under_reset  = 0;

  // bit to configure all uvcs with zero delays to create high bw test
  rand bit              zero_delays;

  // reg model & q of valid csr addresses
  RAL_T                 ral;
  bit [TL_AW-1:0]       csr_addrs[$];
  addr_range_t          mem_ranges[$];
  // mem access support, if not enabled, will trigger error
  bit                   en_mem_byte_write = 0;
  bit                   en_mem_read       = 1;

  // ral base address and size
  bit [TL_AW-1:0]       csr_base_addr;     // base address where csr map begins
  bit [TL_AW:0]         csr_addr_map_size; // csr addr region allocated to the ip, max: 1 << TL_AW

  // clk_rst_if & freq
  virtual clk_rst_if    clk_rst_vif;
  rand clk_freq_mhz_e   clk_freq_mhz;

  // set zero_delays 40% of the time
  constraint zero_delays_c {
    zero_delays dist {1'b0 := 6, 1'b1 := 4};
  }

  `uvm_object_param_utils_begin(dv_base_env_cfg #(RAL_T))
    `uvm_field_int   (is_active,                    UVM_DEFAULT)
    `uvm_field_int   (en_scb,                       UVM_DEFAULT)
    `uvm_field_int   (en_cov,                       UVM_DEFAULT)
    `uvm_field_int   (zero_delays,                  UVM_DEFAULT)
    `uvm_field_int   (csr_base_addr,                UVM_DEFAULT)
    `uvm_field_int   (csr_addr_map_size,            UVM_DEFAULT)
    `uvm_field_enum  (clk_freq_mhz_e, clk_freq_mhz, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    initialize_csr_addr_map_size();
    `DV_CHECK_NE_FATAL(csr_addr_map_size, 0, "csr_addr_map_size can't be 0")
    // use locally randomized csr base address, unless provided as arg to this function
    if (csr_base_addr != '1) begin
      bit is_aligned;
      this.csr_base_addr = csr_base_addr;
      // check alignment
      is_aligned = ~|(this.csr_base_addr & (this.csr_addr_map_size - 1));
      `DV_CHECK_EQ_FATAL(is_aligned, 1'b1)
    end else begin
      // base address needs to be aligned to csr_addr_map_size
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(csr_base_addr,
                                         ~|(csr_base_addr & (csr_addr_map_size - 1));)
      this.csr_base_addr = csr_base_addr;
    end
    // build the ral model
    if (has_ral) begin
      ral = RAL_T::type_id::create("ral");
      ral.build(this.csr_base_addr);
      apply_ral_fixes();
    end
  endfunction

  // This function must be implemented in extended class to
  // initialize value of csr_addr_map_size member
  virtual function void initialize_csr_addr_map_size();
    `uvm_fatal(`gfn, "This task must be implemented in the extended class!")
  endfunction : initialize_csr_addr_map_size

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
