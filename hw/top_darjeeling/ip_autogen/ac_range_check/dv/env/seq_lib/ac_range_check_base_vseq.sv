// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_base_vseq extends cip_base_vseq #(
    .RAL_T               (ac_range_check_reg_block),
    .CFG_T               (ac_range_check_env_cfg),
    .COV_T               (ac_range_check_env_cov),
    .VIRTUAL_SEQUENCER_T (ac_range_check_virtual_sequencer)
  );
  `uvm_object_utils(ac_range_check_base_vseq)

  // Various knobs to enable certain routines
  bit do_ac_range_check_init = 1'b1;

  // Configuration variables
  rand ac_range_check_dut_cfg dut_cfg;

  // Constraints
  extern constraint tl_main_vars_c;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern task dut_init(string reset_kind = "HARD");
  extern task ac_range_check_init();
  extern task cfg_range_base();
  extern task cfg_range_limit();
  extern task cfg_range_perm();
  extern task cfg_range_racl_policy();
  extern task send_single_tl_unfilt_tr(tl_main_vars_t main_vars);
  extern task tl_filt_device_auto_resp(int min_rsp_delay = 0, int max_rsp_delay = 80,
    int rsp_abort_pct = 25, int d_error_pct = 0, int d_chan_intg_err_pct = 0);
endclass : ac_range_check_base_vseq


// Keep the TL transactions randomized by default, this can be overridden easily by derived
// sequences if needed as declared as soft constraints.
constraint ac_range_check_base_vseq::tl_main_vars_c {
  soft dut_cfg.tl_main_vars.rand_write == 1;
  soft dut_cfg.tl_main_vars.rand_addr  == 1;
  soft dut_cfg.tl_main_vars.rand_mask  == 1;
  soft dut_cfg.tl_main_vars.rand_data  == 1;
}

function ac_range_check_base_vseq::new(string name="");
  super.new(name);
  dut_cfg = ac_range_check_dut_cfg::type_id::create("dut_cfg");
endfunction : new

task ac_range_check_base_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init();
  if (do_ac_range_check_init) begin
    ac_range_check_init();
  end

  // Spawns off a thread to auto-respond to incoming TL accesses on the Filtered host interface.
  tl_filt_device_auto_resp();
endtask : dut_init

task ac_range_check_base_vseq::ac_range_check_init();
  cfg_range_base();
  cfg_range_limit();
  cfg_range_perm();
  cfg_range_racl_policy();
endtask : ac_range_check_init

task ac_range_check_base_vseq::cfg_range_base();
  foreach (dut_cfg.range_base[i]) begin
    ral.range_base[i].set(dut_cfg.range_base[i]);
    csr_update(.csr(ral.range_base[i]));
  end
endtask : cfg_range_base

task ac_range_check_base_vseq::cfg_range_limit();
  foreach (dut_cfg.range_limit[i]) begin
    ral.range_limit[i].set(dut_cfg.range_limit[i]);
    csr_update(.csr(ral.range_limit[i]));
  end
endtask : cfg_range_limit

task ac_range_check_base_vseq::cfg_range_perm();
  foreach (dut_cfg.range_perm[i]) begin
    ral.range_perm[i].set({
      prim_mubi_pkg::mubi4_bool_to_mubi(dut_cfg.range_perm[i].log_denied_access),
      prim_mubi_pkg::mubi4_bool_to_mubi(dut_cfg.range_perm[i].execute_access   ),
      prim_mubi_pkg::mubi4_bool_to_mubi(dut_cfg.range_perm[i].write_access     ),
      prim_mubi_pkg::mubi4_bool_to_mubi(dut_cfg.range_perm[i].read_access      ),
      prim_mubi_pkg::mubi4_bool_to_mubi(dut_cfg.range_perm[i].enable           )
    });
    csr_update(.csr(ral.range_perm[i]));
  end
endtask : cfg_range_perm

task ac_range_check_base_vseq::cfg_range_racl_policy();
  foreach (dut_cfg.range_racl_policy[i]) begin
    ral.range_racl_policy_shadowed[i].set(dut_cfg.range_racl_policy[i]);
    // Shodowed register: the 2 writes are automatcally managed by the csr_utils_pkg
    csr_update(.csr(ral.range_racl_policy_shadowed[i]));
  end
endtask : cfg_range_racl_policy

task ac_range_check_base_vseq::send_single_tl_unfilt_tr(tl_main_vars_t main_vars);
  tl_host_single_seq tl_unfilt_host_seq;
  `uvm_create_on(tl_unfilt_host_seq, p_sequencer.tl_unfilt_sqr)
  `DV_CHECK_RANDOMIZE_WITH_FATAL( tl_unfilt_host_seq,
                                  (!main_vars.rand_write) -> (write == main_vars.write);
                                  (!main_vars.rand_addr ) -> (addr  == main_vars.addr);
                                  (!main_vars.rand_mask ) -> (mask  == main_vars.mask);
                                  (!main_vars.rand_data ) -> (data  == main_vars.data);)

  csr_utils_pkg::increment_outstanding_access();
  `uvm_info(`gfn, "Starting tl_unfilt_host_seq", UVM_MEDIUM)
  `DV_SPINWAIT(`uvm_send(tl_unfilt_host_seq), "Timed out when sending fetch request")
  csr_utils_pkg::decrement_outstanding_access();
endtask : send_single_tl_unfilt_tr

task ac_range_check_base_vseq::tl_filt_device_auto_resp(
    int min_rsp_delay       = 0,
    int max_rsp_delay       = 80,
    int rsp_abort_pct       = 25,
    int d_error_pct         = 0,
    int d_chan_intg_err_pct = 0
  );
  cip_tl_device_seq tl_filt_device_seq;
  tl_filt_device_seq = cip_tl_device_seq::type_id::create("tl_filt_device_seq");
  tl_filt_device_seq.min_rsp_delay = min_rsp_delay;
  tl_filt_device_seq.max_rsp_delay = max_rsp_delay;
  tl_filt_device_seq.rsp_abort_pct = rsp_abort_pct;
  tl_filt_device_seq.d_error_pct = d_error_pct;
  tl_filt_device_seq.d_chan_intg_err_pct = d_chan_intg_err_pct;
  `DV_CHECK_RANDOMIZE_FATAL(tl_filt_device_seq)
  `uvm_info(`gfn, "Starting tl_filt_device_seq", UVM_MEDIUM)
  // This fork is required as it will loop indefinitely
  fork
    tl_filt_device_seq.start(p_sequencer.tl_filt_sqr);
  join_none
endtask : tl_filt_device_auto_resp
