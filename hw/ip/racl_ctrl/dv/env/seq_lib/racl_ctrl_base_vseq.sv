// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_base_vseq
  extends cip_base_vseq #(.RAL_T               (racl_ctrl_reg_block),
                          .CFG_T               (racl_ctrl_env_cfg),
                          .COV_T               (racl_ctrl_env_cov),
                          .VIRTUAL_SEQUENCER_T (racl_ctrl_virtual_sequencer));

  `uvm_object_utils(racl_ctrl_base_vseq)

  // Handles to the sequencers for the internal and external error log agents
  racl_error_log_sequencer internal_error_log_sequencer_h;
  racl_error_log_sequencer external_error_log_sequencer_h;

  extern function new (string name="");
  extern function uvm_object clone();
  extern task body();
  extern task post_start();

  // Create a child sequence by name, copying sequencer handles across. Overridden from dv_base_seq.
  extern function uvm_sequence create_seq_by_name(string name);

  // Occasionally write 1 to the the error_log register, which will clear the valid bit (clearing
  // the error). Stop once the stopping flag goes high.
  extern local task clear_error_log();

  // The sequences that we send to the two error log agents. These are started at the start of
  // body() but then told to stop (and waited for) in post_start().
  local racl_error_log_sporadic_seq int_seq, ext_seq;

  // Once the body of this sequence has completed, this bit gets set (which tells the
  // clear_error_log background sequence to stop)
  local bit stopping;

  // This flag gets set by clear_error_log when it is still running.
  local bit clear_error_log_running;
endclass

function racl_ctrl_base_vseq::new (string name="");
  super.new(name);

  int_seq = racl_error_log_sporadic_seq::type_id::create("int_seq");
  ext_seq = racl_error_log_sporadic_seq::type_id::create("ext_seq");
endfunction

function uvm_object racl_ctrl_base_vseq::clone();
  racl_ctrl_base_vseq ret;
  `downcast(ret, super.clone());

  ret.internal_error_log_sequencer_h = internal_error_log_sequencer_h;
  ret.external_error_log_sequencer_h = external_error_log_sequencer_h;

  return ret;
endfunction

task racl_ctrl_base_vseq::body();
  `DV_CHECK_FATAL(internal_error_log_sequencer_h)
  `DV_CHECK_FATAL(external_error_log_sequencer_h)

  // Start "sporadic" sequences on the two error log agents. These are spawned into background
  // threads which are asked to stop in the post_start() task (which will run when the body() task
  // has completed, including any subclass implementation)
  fork
    int_seq.start(internal_error_log_sequencer_h, this);
    ext_seq.start(external_error_log_sequencer_h, this);
    clear_error_log();
  join_none
endtask

task racl_ctrl_base_vseq::post_start();
  fork
    int_seq.request_end();
    ext_seq.request_end();
  join

  // Once the error log sequences have finished, wait one cycle for any error log values to make it
  // to the register file. Then set the stopping flag. This will cause the clear_error_log task to
  // try one more time to clear any log and then exit.
  cfg.clk_rst_vif.wait_clks_or_rst(1);
  stopping = 1'b1;
  wait(!clear_error_log_running);

  super.post_start();
endtask

function uvm_sequence racl_ctrl_base_vseq::create_seq_by_name(string name);
  uvm_sequence        base_ret = super.create_seq_by_name(name);
  racl_ctrl_base_vseq ret;

  `downcast(ret, base_ret)
  `DV_CHECK_FATAL(ret != null)

  ret.internal_error_log_sequencer_h = internal_error_log_sequencer_h;
  ret.external_error_log_sequencer_h = external_error_log_sequencer_h;

  return ret;
endfunction

task racl_ctrl_base_vseq::clear_error_log();
  dv_base_reg error_log_reg;
  dv_base_reg_field valid_field;

  if (clear_error_log_running) `uvm_fatal(`gfn, "Nested call to clear_error_log")
  clear_error_log_running = 1'b1;

  error_log_reg = cfg.ral.get_dv_base_reg_by_name("error_log");
  if (!error_log_reg) `uvm_fatal(`gfn, "Cannot find the ERROR_LOG register.")

  valid_field = error_log_reg.get_field_by_name("valid");
  if (!valid_field) `uvm_fatal(`gfn, "Cannot find a VALID field in the ERROR_LOG register.")

  while (!stopping) begin
    uvm_status_e status;
    uvm_reg_data_t field_value;

    // Insert a gap between each time we consider clearing the logged error. If the stopping flag
    // goes high, stop waiting immediately (but possibly still clear errors)
    fork begin : isolation_fork
      fork
        #100ns;
        wait(stopping);
      join_any
      disable fork;
    end join

    // We can clear the error_log.valid flag by writing 1 to the register. But we don't want to do
    // this every iteration of the loop: the TL traffic will get in the way of other users. Instead
    // of doing that, we only clear the flag if it was previously set.
    valid_field.peek(status, field_value, .kind("BkdrRegPathRtl"));
    if (status != UVM_IS_OK) begin
      `uvm_error(`gfn, "Failed to peek at ERORR_LOG.VALID.")
      field_value = 1'b1;
    end

    if (field_value) error_log_reg.write(status, 1, .prior(100));

    if (status != UVM_IS_OK && !cfg.under_reset) begin
      `uvm_error(`gfn, "Failed to write error_log register")
    end

    // Pause this task if we have gone into reset, but drop out of the pause if stopping becomes
    // true (in which case, the clear_error_log task will stop).
    wait(stopping || !cfg.under_reset);
  end

  clear_error_log_running = 1'b0;
endtask
