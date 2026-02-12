// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A base environment configuration that is used for all OpenTitan environments.

class dv_base_env_cfg #(type RAL_T = dv_base_reg_block) extends uvm_object;

  // True if the environment is active (and thus drives sequences items to the dut). This is the
  // default.
  bit is_active = 1;

  // True if the scoreboard should be enabled. If it is false, the scoreboard still runs, but should
  // ignore its checks.
  bit en_scb = 1;

  // True if the scoreboard should check memory read transactions and predict memory updates from
  // write transactions.
  bit en_scb_mem_chk = 1;

  // Enable functional coverage collection. This causes monitors and scoreboards to collect coverage
  // (through a dv_base_env_cov object).
  bit en_cov = 0;

  // Enable CDC instrumentation
  bit en_dv_cdc = 0;

  // A bit that is true if the environment is currently under reset. This should controlled by
  // calling the reset_asserted and reset_deasserted functions. By default,
  // dv_base_scoreboard::monitor_reset maintains this value.
  bit under_reset = 0;

  // A flag to show that the initialize method has been called. This is protected (rather than
  // local) to allow specialised environments set it to avoid the initialize method being called.
  protected bit is_initialized = 0;

  // The scope and runtime of a existing test can be reduced by setting this variable. This is
  // useful to keep the runtime down especially in time-sensitive runs such as CI, which is meant
  // to check the code health and not find design bugs. It is set via plusarg and retrieved in
  // `dv_base_test`.
  bit smoke_test = 0;

  // If this is true, all UVCs should run with zero delays, which creates a high bandwidth test.
  rand bit zero_delays;

  // A queue of the names of RAL models that should be created in the `initialize` function. Related
  // agents and adapters will be created in the environment as well as connecting them with the
  // scoreboard.
  //
  // To add another RAL model, a subclass of dv_base_env_cfg should implement initialize and add its
  // name before calling super.initialize.
  //
  // The collection of RAL model names is used as an index in ral_models, clk_rst_vifs and
  // clk_freqs_mhz.
  string ral_model_names[$] = {RAL_T::type_name};

  // A RAL model for each name in ral_model_names.
  dv_base_reg_block ral_models[string];

  // A clock and reset interface for each name in ral_model_names. An item is the clock and reset
  // that should be used for the associated TL interface.
  virtual clk_rst_if clk_rst_vifs[string];

  // Clock frequencies for the TL interfaces indexed by ral_model_names.
  rand uint clk_freqs_mhz[string];

  // The "default" RAL's register model. This corresponds to RAL_T::type_name as a model name, and
  // the variable is of type RAL_T (a more specialised class) to simplify access.
  RAL_T ral;

  // The interface for the clock and reset assoicated with the default RAL.
  virtual clk_rst_if clk_rst_vif;

  // The frequency of the clock and reset assoicated with the default RAL.
  rand uint clk_freq_mhz;

  // Set zero_delays 40% of the time
  extern constraint zero_delays_c;

  // Constrain frequencies of the various clocks.
  extern constraint clk_freq_mhz_c;

  `uvm_object_param_utils_begin(dv_base_env_cfg #(RAL_T))
    `uvm_field_int              (is_active,       UVM_DEFAULT)
    `uvm_field_int              (en_scb,          UVM_DEFAULT)
    `uvm_field_int              (en_scb_mem_chk,  UVM_DEFAULT)
    `uvm_field_int              (en_cov,          UVM_DEFAULT)
    `uvm_field_int              (en_dv_cdc,       UVM_DEFAULT)
    `uvm_field_int              (smoke_test,      UVM_DEFAULT)
    `uvm_field_int              (zero_delays,     UVM_DEFAULT)
    `uvm_field_queue_string     (ral_model_names, UVM_DEFAULT)
    `uvm_field_aa_object_string (ral_models,      UVM_DEFAULT)
    `uvm_field_aa_int_string    (clk_freqs_mhz,   UVM_DEFAULT)
  `uvm_object_utils_end

  extern function new (string name="");

  extern function void pre_randomize();
  extern function void post_randomize();

  // Initialise the object with RAL models and set it up for randomisation
  //
  // This is virtual, allowing subclasses to set up list_of_alerts and num_interrupts.
  extern virtual function void initialize(bit [BUS_AW-1:0] csr_base_addr = '1);

  // Set pre-build RAL knobs.
  //
  // This method enables setting pre-build config knobs that can be used to control how the RAL
  // sub-structures are created.
  extern protected virtual function void pre_build_ral_settings(dv_base_reg_block ral);

  // Perform post-build, pre-lock modifications to the RAL.
  //
  // For some registers / fields, the correct access policies or reset values may not be set. Fixes
  // like those can be made with this method.
  extern protected virtual function void post_build_ral_settings(dv_base_reg_block ral);

  // Update the under_reset flag to match the fact that reset has been asserted. This is currently
  // driven by dv_base_scoreboard::monitor_reset.
  extern virtual function void reset_asserted();

  // Update the under_reset flag to match the fact that reset is no longer asserted. This is
  // currently driven by dv_base_scoreboard::monitor_reset.
  extern virtual function void reset_deasserted();

  // Create missing RAL models and set their base addresses based on the supplied arg.
  //
  // csr_base_addr is the base address to set to the RAL models. If it is all 1s, then we treat that
  // as an indication to randomize the base address internally instead.
  extern local function void make_ral_models(bit [BUS_AW-1:0] csr_base_addr);

  // Create the named RAL model and set its base address based on csr_base_addr. This randomises as
  // described in make_ral_models.
  extern local function void make_ral_model(string           ral_model_name,
                                            bit [BUS_AW-1:0] csr_base_addr);

  // Create the named register block. This protected function is virtual to allow subclasses to
  // customise how the register block is created.
  extern protected virtual function dv_base_reg_block create_ral_by_name(string name);
endclass

constraint dv_base_env_cfg::zero_delays_c {
  zero_delays dist {1'b0 := 6, 1'b1 := 4};
}

constraint dv_base_env_cfg::clk_freq_mhz_c {
  `DV_COMMON_CLK_CONSTRAINT(clk_freq_mhz)
  foreach (clk_freqs_mhz[i]) {
    `DV_COMMON_CLK_CONSTRAINT(clk_freqs_mhz[i])
  }
}

function dv_base_env_cfg::new (string name="");
  super.new(name);
endfunction

function void dv_base_env_cfg::pre_randomize();
  if (!is_initialized) `uvm_fatal(`gfn, "Run initialize() before randomizing this object.")
endfunction

function void dv_base_env_cfg::post_randomize();
  if (clk_freqs_mhz.size > 0) begin
    `DV_CHECK_FATAL(clk_freqs_mhz.exists(RAL_T::type_name))
    clk_freqs_mhz[RAL_T::type_name] = clk_freq_mhz;
  end
endfunction

function void dv_base_env_cfg::initialize(bit [BUS_AW-1:0] csr_base_addr = '1);
  is_initialized = 1'b1;

  // build the ral model
  make_ral_models(csr_base_addr);

  // add items to clk_freqs_mhz before randomizing it
  foreach (ral_model_names[i]) begin
    clk_freqs_mhz[ral_model_names[i]] = 0;
  end
endfunction

function void dv_base_env_cfg::pre_build_ral_settings(dv_base_reg_block ral);
  // This is an empty function that a subclass can override
endfunction

function void dv_base_env_cfg::post_build_ral_settings(dv_base_reg_block ral);
  // This is an empty function that a subclass can override
endfunction

function void dv_base_env_cfg::reset_asserted();
  this.under_reset = 1;
  csr_utils_pkg::reset_asserted();
endfunction

function void dv_base_env_cfg::reset_deasserted();
  this.under_reset = 0;
  csr_utils_pkg::reset_deasserted();
endfunction

function void dv_base_env_cfg::make_ral_models(bit [BUS_AW-1:0] csr_base_addr);
  foreach (ral_model_names[i]) make_ral_model(ral_model_names[i], csr_base_addr);
  `DV_CHECK_FATAL(ral_models.exists(RAL_T::type_name))
endfunction

function void dv_base_env_cfg::make_ral_model(string           ral_model_name,
                                              bit [BUS_AW-1:0] csr_base_addr);
  dv_base_reg_block reg_blk;
  bit randomize_base_addr = &csr_base_addr;

  if (ral_models.exists(ral_model_name)) begin
    // If a model for this name already exists, set reg_blk to point at it.
    reg_blk = ral_models[ral_model_name];
  end else begin
    // If a model for this name doesn't already exist, we should make one.
    reg_blk = create_ral_by_name(ral_model_name);

    // Build the register block with an arbitrary base address (we choose 0). We'll change it
    // later.
    pre_build_ral_settings(reg_blk);
    reg_blk.build(.base_addr(0), .csr_excl(null));
    reg_blk.addr_width = BUS_AW;
    reg_blk.data_width = bus_params_pkg::BUS_DW;
    reg_blk.be_width = bus_params_pkg::BUS_DBW;
    post_build_ral_settings(reg_blk);
    reg_blk.lock_model();

    ral_models[ral_model_name] = reg_blk;
    if (reg_blk.get_name() == RAL_T::type_name) `downcast(ral, reg_blk)
  end

  // At this point, either the model existed already or we've just created and locked it. In
  // either case, it should now be locked.
  if (!reg_blk.is_locked()) begin
    `uvm_fatal(`gfn, $sformatf("ral_models[%s] is not locked.", ral_model_name))
  end

  // Since the model is locked, we know its layout. Set the base address for the register block.
  reg_blk.set_base_addr(.base_addr(`UVM_REG_ADDR_WIDTH'(csr_base_addr)),
                        .randomize_base_addr(randomize_base_addr));
  ral_models[ral_model_name] = reg_blk;
endfunction

function dv_base_reg_block dv_base_env_cfg::create_ral_by_name(string name);
  uvm_object        obj;
  uvm_factory       factory;
  dv_base_reg_block ral;

  factory = uvm_factory::get();
  obj = factory.create_object_by_name(.requested_type_name(name), .name(name));
  if (obj == null) begin
    // print factory overrides to help debug
    factory.print();
    `uvm_fatal(`gfn,
               $sformatf({"Could not create %0s as a RAL model. ",
                          "See above for a list of type/instance overrides"},
                         name))
  end
  if (!$cast(ral, obj)) begin
    `uvm_fatal(`gfn, $sformatf("Cast failed - %0s is not a dv_base_reg_block", name))
  end
  return ral;
endfunction
