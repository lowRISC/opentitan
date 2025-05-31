// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_lock_range_vseq extends ac_range_check_smoke_vseq;
  `uvm_object_utils(ac_range_check_lock_range_vseq)

  // ---------------------------------------------------------------------------
  // Random knobs for every range
  // ---------------------------------------------------------------------------
  rand bit [DataWidth-1:0] base  [NUM_RANGES];
  rand bit [DataWidth-1:0] limit [NUM_RANGES];
  rand bit [2:0]           perm  [NUM_RANGES]; // {exec, write, read}
  rand bit                 enable[NUM_RANGES];

  // Second set of values used in the re-program step
  rand bit [DataWidth-1:0] base_new  [NUM_RANGES];
  rand bit [DataWidth-1:0] limit_new [NUM_RANGES];
  rand bit [2:0]           perm_new  [NUM_RANGES];
  rand bit                 enable_new[NUM_RANGES];

  // One-Hot mask indicating which indices are locked
  rand bit [NUM_RANGES-1:0] lock_mask;

  // Random delay in **clock cycles** before the re-program phase begins.
  rand int unsigned reprogram_delay_clks;


  // ---------------------------------------------------------------------------
  // Constraints
  // ---------------------------------------------------------------------------
  constraint addr_pairs_c {
    foreach (base[i]) {
      // 16-Byte alignment
      base      [i][3:0] == 0;
      limit     [i][3:0] == 0;
      base_new  [i][3:0] == 0;
      limit_new [i][3:0] == 0;

      // Forward ranges only
      limit     [i] > base     [i];
      limit_new [i] > base_new [i];
    }
  }

  constraint mask_c {
     // at least one lock and one enable
    lock_mask   != 0;
  }
  constraint reprogram_delay_clks_c { reprogram_delay_clks inside {[20:100]}; }

  // ---------------------------------------------------------------------------
  extern function new(string name = "ac_range_check_lock_range_vseq");
  extern virtual task body();
  extern virtual task configure_range(int unsigned        idx,
                                      bit [DataWidth-1:0] base,
                                      bit [DataWidth-1:0] limit,
                                      bit [2:0]           perm,
                                      bit                 en);

endclass : ac_range_check_lock_range_vseq

// -----------------------------------------------------------------------------
function ac_range_check_lock_range_vseq::new(string name);
  super.new(name);
endfunction

// -----------------------------------------------------------------------------
// Helper that programs a single range using the same RAL/`csr_update` pattern
// used in ac_range_check_base_vseq.
// -----------------------------------------------------------------------------
task ac_range_check_lock_range_vseq::configure_range(
    int unsigned        idx,
    bit [DataWidth-1:0] base,
    bit [DataWidth-1:0] limit,
    bit [2:0]           perm,
    bit                 en);

  `uvm_info(`gfn, $sformatf("Configuring range index: %0d", idx), UVM_MEDIUM)

  // RANGE_BASE_x
  ral.range_base[idx].set(base);
  csr_update(.csr(ral.range_base[idx]));

  // RANGE_LIMIT_x
  ral.range_limit[idx].set(limit);
  csr_update(.csr(ral.range_limit[idx]));

  // RANGE_ATTR_x broken down into fields
  ral.range_attr[idx].execute_access.set(mubi4_bool_to_mubi(perm[2]));
  ral.range_attr[idx].write_access.set  (mubi4_bool_to_mubi(perm[1]));
  ral.range_attr[idx].read_access.set   (mubi4_bool_to_mubi(perm[0]));
  ral.range_attr[idx].enable.set        (mubi4_bool_to_mubi(en));
  csr_update(.csr(ral.range_attr[idx]));

  // Disable RACL side effects for simplicity.
  ral.range_racl_policy_shadowed[idx].set(32'hFFFF_FFFF);
  csr_update(.csr(ral.range_racl_policy_shadowed[idx]));
endtask : configure_range

// -----------------------------------------------------------------------------
// Main stimulus
// -----------------------------------------------------------------------------
task ac_range_check_lock_range_vseq::body();
  // Local variable just for the body task
  bit reprogram_done = 0;
  bit [3:0]  mubi4_execute;
  bit [3:0]  mubi4_write;
  bit [3:0]  mubi4_read;
  bit [3:0]  mubi4_enable;
  bit [19:0] mubi4_attr;

  `uvm_info(`gfn, "Starting ac_range_check_lock_range_seq", UVM_LOW)

  `DV_CHECK_RANDOMIZE_FATAL(this)
  this.base.rand_mode(0);
  this.limit.rand_mode(0);
  this.perm.rand_mode(0);
  this.enable.rand_mode(0);
  this.base_new.rand_mode(0);
  this.limit_new.rand_mode(0);
  this.perm_new.rand_mode(0);
  this.enable_new.rand_mode(0);
  this.lock_mask.rand_mode(0);
  this.reprogram_delay_clks.rand_mode(0);

  //------------------------------------------------------------------
  // Step 1 : Configure every range once with *initial* values.
  //------------------------------------------------------------------
  foreach (base[i]) begin
    configure_range(i, base[i], limit[i], perm[i], enable[i]);
  end

  //------------------------------------------------------------------
  // Step 2 : Lock a random subset by clearing RANGE_REGWEN_x.
  //------------------------------------------------------------------
  foreach (lock_mask[i]) begin
    if (lock_mask[i]) begin
      `uvm_info(`gfn, $sformatf("Locking range index: %0d", i), UVM_MEDIUM)
      ral.range_regwen[i].set(32'h0);
      csr_update(.csr(ral.range_regwen[i]));
    end

    if (cfg.en_cov) cov.sample_range_lock_cg(i, enable[i], lock_mask[i]);
  end

  //------------------------------------------------------------------
  // Step 3 : Kick off traffic that runs until re-programming completes. A
  // boolean flag `reprogram_done` communicates between the two forked threads.
  //------------------------------------------------------------------
  fork
    // Traffic thread - keep going until the flag is asserted.
    begin : traffic_thread
      while (!reprogram_done) begin
        `DV_CHECK_RANDOMIZE_FATAL(this)
        //std::randomize(tl_main_vars);
        send_single_tl_unfilt_tr(0);
      end
    end

    // Re-Program thread
    begin : reprogram_thread
      cfg.clk_rst_vif.wait_clks(reprogram_delay_clks);
      foreach (base_new[i]) begin
        `uvm_info(`gfn, $sformatf("Attempting to reprogram Range index: %0d", i), UVM_MEDIUM)
        if (lock_mask[i]) begin
          mubi4_execute = mubi4_bool_to_mubi(perm_new[i][2]);
          mubi4_write   = mubi4_bool_to_mubi(perm_new[i][1]);
          mubi4_read    = mubi4_bool_to_mubi(perm_new[i][0]);
          mubi4_enable  = mubi4_bool_to_mubi(enable_new[i] );

          mubi4_attr = {MuBi4True, mubi4_execute, mubi4_write, mubi4_read, mubi4_enable};

          // Attempt direct writes to a locked range; they should be ignored.
          // Direct access is done here since if we attempt to set ral object
          // it will fail
          csr_wr(.ptr(ral.range_base [i]), .value(base_new[i] ));
          csr_wr(.ptr(ral.range_limit[i]), .value(limit_new[i]));
          csr_wr(.ptr(ral.range_attr [i]), .value(mubi4_attr  ));
        end else begin
          // Unlocked ranges get a full, legal re-configuration.
          configure_range(i, base_new[i], limit_new[i], perm_new[i], enable_new[i]);
        end
      end
      reprogram_done = 1;
    end
  join

  //------------------------------------------------------------------
  // Step 4 : Read back registers and verify lock behaviour.
  //------------------------------------------------------------------
  foreach (base[i]) begin
    uvm_reg_data_t act_base , act_lim , act_attr;
    csr_rd(.ptr(ral.range_base [i]), .value(act_base));
    csr_rd(.ptr(ral.range_limit[i]), .value(act_lim));
    csr_rd(.ptr(ral.range_attr [i]), .value(act_attr));

    `uvm_info(`gfn, $sformatf("Readback range index: %0d", i), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("act_base: 0x%0h, act_lim: 0x%0h, act_attr: 0x%0h",
                               act_base, act_lim, act_attr), UVM_MEDIUM)

    if (lock_mask[i]) begin
      mubi4_execute = mubi4_bool_to_mubi(perm[i][2]);
      mubi4_write   = mubi4_bool_to_mubi(perm[i][1]);
      mubi4_read    = mubi4_bool_to_mubi(perm[i][0]);
      mubi4_enable  = mubi4_bool_to_mubi(enable[i] );
      mubi4_attr    = {MuBi4True, mubi4_execute, mubi4_write, mubi4_read, mubi4_enable};

      `uvm_info(`gfn, $sformatf("exp: base: 0x%0h, lim: 0x%0h, attr: 0x%0h",
                                      base [i], limit[i], mubi4_attr), UVM_MEDIUM)

      // Locked regions must still show the *initial* values.
      `DV_CHECK_EQ(act_base, base [i],   $sformatf("Range %0d base locked", i));
      `DV_CHECK_EQ(act_lim , limit[i],   $sformatf("Range %0d limit locked",i));
      `DV_CHECK_EQ(act_attr, mubi4_attr, $sformatf("Range %0d attr locked", i));
    end else begin
      mubi4_execute = mubi4_bool_to_mubi(perm_new[i][2]);
      mubi4_write   = mubi4_bool_to_mubi(perm_new[i][1]);
      mubi4_read    = mubi4_bool_to_mubi(perm_new[i][0]);
      mubi4_enable  = mubi4_bool_to_mubi(enable_new[i] );
      mubi4_attr    = {MuBi4True, mubi4_execute, mubi4_write, mubi4_read, mubi4_enable};

      `uvm_info(`gfn, $sformatf("base_new: 0x%0h, lim_new: 0x%0h, attr_new: 0x%0h",
                                      base_new [i], limit_new[i], mubi4_attr), UVM_MEDIUM)

      // Unlocked regions should now hold the *new* values.
      `DV_CHECK_EQ(act_base, base_new [i],
                   $sformatf("Range %0d unlocked - base did not update",  i));
      `DV_CHECK_EQ(act_lim , limit_new[i],
                   $sformatf("Range %0d unlocked - limit did not update", i));
      `DV_CHECK_EQ(act_attr, mubi4_attr,
                   $sformatf("Range %0d unlocked - attr did not update", i));
    end
  end
endtask : body
