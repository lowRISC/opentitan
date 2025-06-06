// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// High-level goal
// ---------------
// - Exercises the *range-locking* feature for AC_RANGE_CHECK.
// - Confirms that once RANGE_REGWEN_x is cleared, subsequent CSR writes to that
//   range are ignored while unlocked ranges continue to accept re-programming.
// - Runs live TLUL traffic throughout to catch any functional regressions.
//
// Key take-aways
// --------------
// - Verifies that locked ranges cannot be modified even by direct CSR writes.
// - Confirms unlocked ranges remain fully programmable.
// - Applies continuous traffic pressure to catch timing or side effect issues.
//------------------------------------------------------------------------------


class ac_range_check_lock_range_vseq extends ac_range_check_smoke_vseq;
  `uvm_object_utils(ac_range_check_lock_range_vseq)

  // ---------------------------------------------------------------------------
  // Random knobs for every range
  // ---------------------------------------------------------------------------
  rand bit [DataWidth-1:0] base  [NUM_RANGES];
  rand bit [DataWidth-1:0] limit [NUM_RANGES];

  rand bit read_perm   [NUM_RANGES];
  rand bit write_perm  [NUM_RANGES];
  rand bit execute_perm[NUM_RANGES];

  // Second set of values used in the re-program step
  rand bit [DataWidth-1:0] base_new  [NUM_RANGES];
  rand bit [DataWidth-1:0] limit_new [NUM_RANGES];

  rand bit read_perm_new   [NUM_RANGES];
  rand bit write_perm_new  [NUM_RANGES];
  rand bit execute_perm_new[NUM_RANGES];

  // Mask indicating which Range Indexes are locked
  rand bit [NUM_RANGES-1:0] lock_mask;

  // Mask indicating which Range Indexes are enabled
  // enable_new is the second set for the re-program step
  rand bit [NUM_RANGES-1:0] enable;
  rand bit [NUM_RANGES-1:0] enable_new;

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
      (limit     [i] - base     [i]) inside {[32'h100:32'h200]};
      (limit_new [i] - base_new [i]) inside {[32'h100:32'h200]};

      // Ensure base  is always less than limit
      base     [i] < limit     [i];
      base_new [i] < limit_new [i];


      if (i == (NUM_RANGES-1)) {
        // This is a catch all since there is a situation where the test fails due to a TB condition
        // which checks for at least 1 TLUL GRANTED transaction. By enabling the write permission
        // for the very last index and forcing a transaction that is guranteed to be GRANTED
        // overcomes this restriction.
        enable[i]     == 1;
        lock_mask[i]  == 1;
        write_perm[i] == 1;
      }
    }
  }

  constraint mask_c {
    // At least one index will be locked in the test. Similarly enable is also set so that there is
    // atleast one index that is enabled
    lock_mask  != 0;
    enable     != 0;
    enable_new != 0;
  }
  constraint reprogram_delay_clks_c { reprogram_delay_clks inside {[0:100]}; }

  // // Standard SV/UVM methods
  extern function new(string name = "");
  extern virtual task body();

endclass : ac_range_check_lock_range_vseq

function ac_range_check_lock_range_vseq::new(string name);
  super.new(name);
endfunction


task ac_range_check_lock_range_vseq::body();
  // Local variable just for the body task
  bit reprogram_done = 0;

  `uvm_info(`gfn, "Starting ac_range_check_lock_range_seq", UVM_LOW)

  `DV_CHECK_RANDOMIZE_FATAL(this)
  this.base.rand_mode(0);
  this.limit.rand_mode(0);
  this.read_perm.rand_mode(0);
  this.write_perm.rand_mode(0);
  this.execute_perm.rand_mode(0);
  this.enable.rand_mode(0);
  this.base_new.rand_mode(0);
  this.limit_new.rand_mode(0);
  this.read_perm_new.rand_mode(0);
  this.write_perm_new.rand_mode(0);
  this.execute_perm_new.rand_mode(0);
  this.enable_new.rand_mode(0);
  this.lock_mask.rand_mode(0);
  this.reprogram_delay_clks.rand_mode(0);

  //------------------------------------------------------------------
  // Step 1 : Configure every range once with *initial* values.
  //------------------------------------------------------------------
  foreach (base[i]) begin
    configure_range(i, base[i], limit[i], read_perm[i], write_perm[i], execute_perm[i], enable[i]);
  end

  //------------------------------------------------------------------
  // Step 2 : Lock a random subset by clearing RANGE_REGWEN_x.
  //------------------------------------------------------------------
  foreach (lock_mask[i]) begin
    if (lock_mask[i]) begin
      `uvm_info(`gfn, $sformatf("Range index: %0d Locked", i), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("enable: %0h", enable[i]), UVM_MEDIUM)
      ral.range_regwen[i].set(32'h0);
      csr_update(.csr(ral.range_regwen[i]));
    end else begin
      `uvm_info(`gfn, $sformatf("Range index: %0d Unlocked", i), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("enable: %0h", enable[i]), UVM_MEDIUM)
    end

    // TODO(#27352): Coverage sampling needs to be moved to scoreboard.
    // Currently in ac_range_check_scoreboard we are seeing TL transactions to range_regwen[i]
    // register being dropped when a write with range_regwen[i] = 1. This needs to be debugged as
    // a write to this register irrespective of the value triggers coverage sampling
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
        send_single_tl_unfilt_tr(0);
      end
    end

    // Re-Program thread
    begin : reprogram_thread
      cfg.clk_rst_vif.wait_clks(reprogram_delay_clks);
      foreach (base_new[i]) begin
        `uvm_info(`gfn, $sformatf("Attempting to reprogram Range index: %0d", i), UVM_MEDIUM)
        if (lock_mask[i]) begin
          int unsigned lsb;

          // The below temp variables are used for setting configuration for each range index.
          bit [MuBi4Width-1:0] mubi4_execute;
          bit [MuBi4Width-1:0] mubi4_write;
          bit [MuBi4Width-1:0] mubi4_read;
          bit [MuBi4Width-1:0] mubi4_enable;
          bit [MuBi4Width-1:0] mubi4_log_denied;

          // Combination word that is needed to program the CSR for each Range Index Attribute
          bit [DataWidth-1:0] mubi4_attr;

          // When range index is locked, the RTL and the RAL are in sync. Which means the RAL model
          // is also locked for the sepcific index and the set methods for fields such as
          // 'ral.range_attr[i].read_access.set(mubi4_bool_to_mubi(read_perm_new[i]));'
          // 'ral.range_attr[i].write_access.set(mubi4_bool_to_mubi(write_perm_new[i]));'
          // will not work. We need to build the attr field explictly and then write new values
          // to the CSRlocation via csr_wr() method for base, limit & attr.
          mubi4_execute    = mubi4_bool_to_mubi(execute_perm_new[i]);
          mubi4_write      = mubi4_bool_to_mubi(write_perm_new[i]  );
          mubi4_read       = mubi4_bool_to_mubi(read_perm_new[i]   );
          mubi4_enable     = mubi4_bool_to_mubi(enable_new[i]      );
          mubi4_log_denied = MuBi4True;

          // The attr register consist of 5 fields namely:
          // log_denied_access, execute_access, write_access, read_access, enable.
          // 'mubi4_attr' is used to build this word that will be written.

          // Variable reset before building the word to be written.
          mubi4_attr = 0;

          // Insert log_denied into correct position
          lsb         = ral.range_attr[i].log_denied_access.get_lsb_pos();
          mubi4_attr |= mubi4_log_denied << lsb;

          // Insert Execute into correct position
          lsb         = ral.range_attr[i].execute_access.get_lsb_pos();
          mubi4_attr |=  mubi4_execute << lsb;

          // Insert Write into correct position
          lsb         = ral.range_attr[i].write_access.get_lsb_pos();
          mubi4_attr |= mubi4_write << lsb;

          // Insert Read into correct position
          lsb         = ral.range_attr[i].read_access.get_lsb_pos();
          mubi4_attr |= mubi4_read  << lsb;

          // Insert enable into correct position
          lsb         = ral.range_attr[i].enable.get_lsb_pos();
          mubi4_attr |= mubi4_enable  << lsb;

          `uvm_info(`gfn, $sformatf("Setting mubi4_attr: 0x%0h", mubi4_attr), UVM_MEDIUM)

          // Attempt direct writes to a locked range; they should be ignored.
          // Direct access is done here. If we attempt to set ral object expected results will not
          // be observed at the interface..
          csr_wr(.ptr(ral.range_base [i]), .value(base_new[i] ));
          csr_wr(.ptr(ral.range_limit[i]), .value(limit_new[i]));
          csr_wr(.ptr(ral.range_attr [i]), .value(mubi4_attr  ));
        end else begin
          // Unlocked ranges get a full, legal re-configuration.
          configure_range(i, base_new[i], limit_new[i], read_perm_new[i], write_perm_new[i],
                          execute_perm_new[i], enable_new[i]);
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

    // Readback is done so that CSR data checks are done in the scoreboard to prove data integrity
    // of the Locked Fields in the CSR. No further check here.

    `uvm_info(`gfn, $sformatf("Readback range index: %0d", i), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("act_base: 0x%0h, act_lim: 0x%0h, act_attr: 0x%0h",
                               act_base, act_lim, act_attr), UVM_MEDIUM)


    // The lock range test fails because of a check in the scoreboard that has not seen a single
    // transaction granted. By sending a TLUL request that gurantees to get granted, The TB
    // condition is satisfied.
    if (i == (NUM_RANGES-1)) begin
      tl_main_vars.addr = base[i];
      tl_main_vars.write = 1;
      send_single_tl_unfilt_tr(0);
    end
  end
endtask : body
