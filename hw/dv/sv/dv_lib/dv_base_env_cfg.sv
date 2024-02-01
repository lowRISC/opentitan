// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_env_cfg #(type RAL_T = dv_base_reg_block) extends uvm_object;

  bit is_active         = 1;
  bit en_scb            = 1; // can be changed at run-time
  bit en_scb_tl_err_chk = 1;
  bit en_scb_mem_chk    = 1;
  bit en_scb_ping_chk   = 1;
  bit en_cov            = 0; // Enable via plusarg, only if coverage collection is turned on.
  bit en_dv_cdc         = 0; // Enable via plusarg.

  local bit will_reset  = 0;
  bit under_reset       = 0;
  bit is_initialized;        // Indicates that the initialize() method has been called.

  // JTAG DMI knob
  // this has to be set test.build
  // before cfg.initialize
  bit use_jtag_dmi = 0;

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
  RAL_T             ral;
  dv_base_reg_block ral_models[string];

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
  rand uint clk_freq_mhz;
  rand uint clk_freqs_mhz[string];

  constraint clk_freq_mhz_c {
    `DV_COMMON_CLK_CONSTRAINT(clk_freq_mhz)
    foreach (clk_freqs_mhz[i]) {
      `DV_COMMON_CLK_CONSTRAINT(clk_freqs_mhz[i])
    }
  }

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
      clk_freqs_mhz[ral_model_names[i]] = 0;
    end
  endfunction

  // Set pre-build RAL knobs.
  //
  // This method enables setting pre-build config knobs that can be used to control how the RAL
  // sub-structures are created.
  protected virtual function void pre_build_ral_settings(dv_base_reg_block ral);
  endfunction

  // Perform post-build, pre-lock modifications to the RAL.
  //
  // For some registers / fields, the correct access policies or reset values may not be set. Fixes
  // like those can be made with this method.
  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
  endfunction

  // This can be used to stop transaction generators either upon reset or in preparation to
  // issue a random reset.
  virtual function bit stop_transaction_generators();
    return this.will_reset || this.under_reset;
  endfunction

  // This can be used to announce the intention to generate a random reset soon, to allow
  // transaction generators to stop, and fire a reset with no outstanding transactions.
  virtual function void set_intention_to_reset();
    `uvm_info(`gfn, "Setting intention to reset", UVM_MEDIUM)
    this.will_reset = 1'b1;
  endfunction

  virtual function void reset_asserted();
    this.under_reset = 1;
    this.will_reset = 0;
    csr_utils_pkg::reset_asserted();
  endfunction

  virtual function void reset_deasserted();
    this.under_reset = 0;
    csr_utils_pkg::reset_deasserted();
  endfunction

  // Creates RAL models and sets their base address based on the supplied arg.
  //
  // csr_base_addr is the base address to set to the RAL models. If it is all 1s, then we treat that
  // as an indication to randomize the base address internally instead.
  virtual function void create_ral_models(bit [bus_params_pkg::BUS_AW-1:0] csr_base_addr = '1);

    foreach (ral_model_names[i]) begin
      string ral_name = ral_model_names[i];
      bit randomize_base_addr = &csr_base_addr;
      dv_base_reg_block reg_blk = create_ral_by_name(ral_name);

      if (reg_blk.get_name() == RAL_T::type_name) `downcast(ral, reg_blk)

      // Build the register block with an arbitrary base address (we choose 0). We'll change it
      // later.
      pre_build_ral_settings(reg_blk);
      reg_blk.build(.base_addr(0), .csr_excl(null));
      reg_blk.addr_width = bus_params_pkg::BUS_AW;
      reg_blk.data_width = bus_params_pkg::BUS_DW;
      reg_blk.be_width = bus_params_pkg::BUS_DBW;
      post_build_ral_settings(reg_blk);
      reg_blk.lock_model();

      // Now the model is locked, we know its layout. Set the base address for the register block.
      reg_blk.set_base_addr(.base_addr(`UVM_REG_ADDR_WIDTH'(csr_base_addr)),
                            .randomize_base_addr(randomize_base_addr));

      // Get list of valid csr addresses (useful in seq to randomize addr as well as in scb checks)
      reg_blk.compute_mapped_addr_ranges();
      reg_blk.compute_unmapped_addr_ranges();
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
