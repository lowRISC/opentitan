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

  // ral base address and size
  bit [bus_params_pkg::BUS_AW-1:0]  csr_base_addr;     // base address where csr map begins
  bit [bus_params_pkg::BUS_AW:0]    csr_addr_map_size; // csr addr region allocated to the ip,
                                                       // max: 1 << bus_params_pkg::BUS_AW

  // clk_rst_if & freq
  virtual clk_rst_if  clk_rst_vif;
  rand clk_freq_mhz_e clk_freq_mhz;

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

  virtual function void initialize(bit [bus_params_pkg::BUS_AW-1:0] csr_base_addr = '1);
    // build the ral model
    if (has_ral) begin
      ral = RAL_T::type_id::create("ral");
      // use base address 0 to build and change it later
      ral.build(.base_addr(0), .csr_excl(null));
      apply_ral_fixes();
      ral.lock_model();
      initialize_dut_addr_space(csr_base_addr);
      // Get list of valid csr addresses (useful in seq to randomize addr as well as in scb checks)
      get_csr_addrs(ral, csr_addrs);
      get_mem_addr_ranges(ral, mem_ranges);
      ral_models.push_back(ral);
    end
  endfunction

  // initialize dut base address and address map size
  // when csr_base_addr is '1, will be randomized based on address map size
  virtual function void initialize_dut_addr_space(
      bit [bus_params_pkg::BUS_AW-1:0] csr_base_addr = '1);

    csr_addr_map_size = ral.get_addr_map_size();
    // use locally randomized csr base address based on csr_addr_map_size,
    // unless provided as arg to this function
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
    ral.default_map.set_base_addr(this.csr_base_addr);
  endfunction : initialize_dut_addr_space

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
