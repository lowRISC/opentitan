// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_env_cfg #(type RAL_T = dv_base_reg_block) extends uvm_object;

  bit is_active         = 1;
  bit en_scb            = 1; // can be changed at run-time
  bit en_scb_tl_err_chk = 1;
  bit en_scb_mem_chk    = 1;
  bit en_cov            = 0; // Enable via plusarg, only if coverage collection is turned on.

  bit under_reset       = 0;
  bit is_initialized;        // Indicates that the initialize() method has been called.

  // The scope and runtime of a existing test can be reduced by setting this variable. This is
  // useful to keep the runtime down especially in time-sensitive runs such as CI, which is meant
  // to check the code health and not find design bugs. It is set via plusarg and retrieved in
  // `dv_base_test`.
  bit smoke_test = 0;

  // bit to configure all uvcs with zero delays to create high bw test
  rand bit zero_delays;

  // set zero_delays 40% of the time
  constraint zero_delays_c {
    zero_delays dist {1'b0 := 6, 1'b1 := 4};
  }

  // reg model & q of valid csr addresses
  RAL_T                             ral;
  dv_base_reg_block                 ral_models[string];
  // A queue of the names of RAL models that should be created in the `initialize` function
  // Related agents, adapters will be created in env as well as connecting them with scb
  // For example, if the IP has an additional RAL model named `ral1`, add it into the list as below
  //   virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
  //     ral_model_names.push_back("ral1");
  //     super.initialize(csr_base_addr);
  string ral_model_names[$] = {RAL_T::type_name};

  // clk_rst_if & freq
  // clk_rst_vif and clk_freq_mhz are used for default clk/rst. If more than one RAL, the other
  // clk_rst_vif and clk_freq_mhz can be found from the associative arrays
  virtual clk_rst_if  clk_rst_vif;
  virtual clk_rst_if  clk_rst_vifs[string];
  rand clk_freq_mhz_e clk_freq_mhz;
  rand clk_freq_mhz_e clk_freqs_mhz[string];

  `uvm_object_param_utils_begin(dv_base_env_cfg #(RAL_T))
    `uvm_field_int   (is_active,   UVM_DEFAULT)
    `uvm_field_int   (en_scb,      UVM_DEFAULT)
    `uvm_field_int   (en_cov,      UVM_DEFAULT)
    `uvm_field_int   (zero_delays, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void pre_randomize();
    `DV_CHECK_FATAL(is_initialized, "Please invoke initialize() before randomizing this object.")
  endfunction

  function void post_randomize();
    if (clk_freqs_mhz.size > 0) begin
      `DV_CHECK_FATAL(clk_freqs_mhz.exists(RAL_T::type_name))
      clk_freqs_mhz[RAL_T::type_name] = clk_freq_mhz;
    end
  endfunction

  virtual function void initialize(bit [bus_params_pkg::BUS_AW-1:0] csr_base_addr = '1);
    is_initialized = 1'b1;

    // build the ral model
    create_ral_models(csr_base_addr);

    // add items to clk_freqs_mhz before randomizing it
    foreach (ral_model_names[i]) begin
      clk_freqs_mhz[ral_model_names[i]] = ClkFreq24Mhz;
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

  virtual function void create_ral_models(bit [bus_params_pkg::BUS_AW-1:0] csr_base_addr = '1);

    foreach (ral_model_names[i]) begin
      string ral_name = ral_model_names[i];
      uvm_reg_addr_t base_addr;
      dv_base_reg_block reg_blk = create_ral_by_name(ral_name);

      if (reg_blk.get_name() == RAL_T::type_name) `downcast(ral, reg_blk)

      // Build the register block with an arbitrary base address (we choose 0). We'll change it
      // later.
      reg_blk.build(.base_addr(0), .csr_excl(null));
      apply_ral_fixes();
      reg_blk.lock_model();

      // Now the model is locked, we know its layout. Set the base address for the register block.
      // The function internally picks a random one if we pass '1 to it, and performs an integrity
      // check on the set address.
      //
      // The definition of base_addr explicitly casts from a bus address to a uvm_reg_addr_t (to
      // correctly handle the case where a bus address is narrower than a uvm_reg_addr_t).
      base_addr = (&csr_base_addr ?
                   {`UVM_REG_ADDR_WIDTH{1'b1}} :
                   {{(`UVM_REG_ADDR_WIDTH - bus_params_pkg::BUS_AW){1'b0}}, csr_base_addr});
      reg_blk.set_base_addr(base_addr);

      // Get list of valid csr addresses (useful in seq to randomize addr as well as in scb checks)
      reg_blk.compute_mapped_addr_ranges();
      reg_blk.compute_unmapped_addr_ranges();
      `uvm_info(msg_id,
                $sformatf("RAL[%0s] mapped addresses: %0p",
                          ral_name, reg_blk.mapped_addr_ranges),
                UVM_HIGH)
      `uvm_info(msg_id,
                $sformatf("RAL[%0s] unmapped addresses: %0p",
                          ral_name, reg_blk.unmapped_addr_ranges),
                UVM_HIGH)
      ral_models[ral_name] = reg_blk;
    end

    if (ral_model_names.size > 0) begin
      `DV_CHECK_FATAL(ral_models.exists(RAL_T::type_name))
    end
  endfunction

  virtual function dv_base_reg_block create_ral_by_name(string name);
    uvm_object        obj;
    uvm_factory       factory;
    dv_base_reg_block ral;

    factory = uvm_factory::get();
    obj = factory.create_object_by_name(.requested_type_name(name), .name(name));
    if (obj == null) begin
      // print factory overrides to help debug
      factory.print();
      `uvm_fatal(msg_id, $sformatf("could not create %0s as a RAL model, see above for a list of \
                                    type/instance overrides", name))
    end
    if (!$cast(ral, obj)) begin
      `uvm_fatal(msg_id, $sformatf("cast failed - %0s is not a dv_base_reg_block", name))
    end
    return ral;
  endfunction
endclass
