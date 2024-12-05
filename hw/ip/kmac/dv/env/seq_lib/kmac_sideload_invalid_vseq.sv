// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sideload invalid key test
class kmac_sideload_invalid_vseq extends kmac_long_msg_and_output_vseq;

  `uvm_object_utils(kmac_sideload_invalid_vseq)
  `uvm_object_new

  // Flag used to indicate when KMAC operation has finished. Consumed by the
  // inject_error task.
  bit kmac_done;

  constraint num_trans_c {
    num_trans inside {[1:20]};
  }

  constraint en_app_c {
    en_app dist {
      0 :/ 3,
      1 :/ 7
    };
  }

  constraint en_sideload_c {
    reg_en_sideload == 1;
  }

  constraint kmac_en_c {
    kmac_en == 1;
  }

  constraint provide_sideload_key_c {
    provide_sideload_key == 1;
  }

  constraint app_mode_c {
    app_mode == AppKeymgr;
  }

  constraint entropy_ready_c {
    entropy_ready == 1;
  }

  constraint disable_err_c {
    kmac_err_type == kmac_pkg::ErrKeyNotValid;
  }

  constraint msg_c {
    msg.size() inside {[1 : 32]};
  }

  constraint output_len_c {
    output_len inside {[1:keccak_block_size]};
  }

  rand kmac_pkg::st_e target_state;

  constraint target_state_c {
    if (en_app) {
      target_state inside {kmac_pkg::StAppCfg, kmac_pkg::StAppMsg, kmac_pkg::StAppOutLen,
                           kmac_pkg::StAppProcess, kmac_pkg::StAppWait};
    } else {
      target_state inside {kmac_pkg::StSw};
    }
  }

  task send_kmac_req();
    // Send KMAC app requests or SW commands to the IP block. When we are done,
    // use the kmac_done variable to flag it to the inject_error task.
    if (en_app) begin
      send_kmac_app_req(app_mode);

      // Wait until we got the response.
      // TODO(lowrisc/opentitan#24739): Currently, when invalidating the key when the
      // app_i.last was received, exiting the StErrorAwaitApp is not possible anymore.
      // After resolving this issue, we simply can wait until we got kmac_done.
      wait(cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.valid &&
           cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.last);
      kmac_done = 1;
    end else begin
      // Issue Start cmd.
      issue_cmd(CmdStart);

      read_regwen_and_rand_write_locked_regs();

      // Write the message into msgfifo.
      write_msg(msg, .blocking(0), .wait_for_fifo_has_capacity(0));

      right_encode(xof_en ? 0 : output_len * 8, output_len_enc);
      write_msg(output_len_enc, .blocking(0), .wait_for_fifo_has_capacity(0));

      // Wait for some cycles after writing message to let internal state settle.
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));

      // Issue Process cmd.
      issue_cmd(CmdProcess);

      // Wait until we are done.
      csr_spinwait(.ptr(ral.intr_state.kmac_done), .exp_data(1'b1));
      // When we are done, there is no point to invalidate the key.
      kmac_done = 1;

      read_regwen_and_rand_write_locked_regs();
    end
  endtask

  task inject_error(string app_fsm_path, string key_valid_path, kmac_pkg::err_t exp_kmac_err);
    // Monitor the KMAC app FSM state. When the target state is reached & the sideload
    // key is valid, invalidate the key. Abort if the send_kmac_req signals with the
    // kmac_done flag that the operation already is finished.
    bit [9:0] curr_state = kmac_pkg::StIdle;
    bit invalidate_key = 0;
    `DV_SPINWAIT_EXIT(
      begin
        // Randomly select a state where we want to invalidate the key,
        // wait until the state is reached and the key is valid.
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(target_state)

        // Wait until we have reached the target state.
        while(curr_state != target_state) begin
          cfg.clk_rst_vif.wait_n_clks(1);
          `DV_CHECK(uvm_hdl_read(app_fsm_path, curr_state))
        end
        // Wait until the sideload key gets valid.
        wait(cfg.keymgr_sideload_agent_cfg.vif.sideload_key.valid);
        invalidate_key = 1;
      end
      ,
      // If we are already finished, abort waiting for FSM state or key valid.
      wait(kmac_done);
    );

    // TODO(lowrisc/opentitan#24739): Currently, when invalidating the key when the
    // app_i.last was received, exiting the StErrorAwaitApp is not possible anymore.
    // After resolving this issue, the last condition can be removed.
    if (invalidate_key && !kmac_done &&
        (!en_app || !cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.last)) begin
      // We got the FSM state, the key is valid, and the operation is not yet done.
      // Invalidate the key and wait for the expected error code.
      `uvm_info(`gfn, $sformatf("invalidated key in state %0b", curr_state), UVM_LOW)
      cfg.key_invalidated = 1;
      `DV_CHECK(uvm_hdl_force(key_valid_path, 0))
      cfg.skip_read_check = 1;
      csr_spinwait(.ptr(ral.err_code), .exp_data(exp_kmac_err));
      `uvm_info(`gfn, "received the expected error code", UVM_LOW)
      cfg.skip_read_check = 0;
      `DV_CHECK(uvm_hdl_release(key_valid_path))
      csr_wr(.ptr(ral.cmd.err_processed), .value(1));
    end else begin
      // Normal operation, wait until KMAC operation has finished.
      wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.rsp_done == 1);
    end
  endtask

  virtual task pre_start();
    do_kmac_init = 0;
    super.pre_start();
  endtask

  virtual task body();
    key_sideload_set_seq sideload_seq;
    string key_valid_path = "tb.dut.keymgr_key_i.valid";
    string app_fsm_path = "tb.dut.u_app_intf.st";
    kmac_pkg::err_t exp_kmac_err = '{valid: 1'b1,
                                     code: kmac_pkg::ErrKeyNotValid,
                                     info: '0};

    `DV_CHECK(uvm_hdl_check_path(key_valid_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", key_valid_path))
    `DV_CHECK(uvm_hdl_check_path(app_fsm_path),
              $sformatf("Hierarchical path %0s appears to be invalid.", app_fsm_path))

    for (int i = 0; i < num_trans; i++) begin
      bit [7:0] share0[];
      bit [7:0] share1[];

      kmac_done = 0;

      cfg.key_invalidated = 0;

      `uvm_info(`gfn, $sformatf("iteration: %0d/%0d", i, num_trans), UVM_LOW)

      `DV_CHECK_RANDOMIZE_FATAL(this)

      kmac_init(.keymgr_app_intf(is_keymgr_app));
      `uvm_info(`gfn, "kmac_init done", UVM_HIGH)

      // Write the cfg_shadowed in the shadow register. The kmac_init function above
      // actually only uses a csr_update which only updates the cfg_shadow register if
      // there is a difference. If we would not doing the csr_wr, the entropy_ready bit
      // does not get set but the HW is waiting for the entropy ready pulse.
      csr_wr(.ptr(ral.cfg_shadowed), .value(`gmv(ral.cfg_shadowed)));

      read_regwen_and_rand_write_locked_regs();

      set_prefix();

      // Set the sideload key.
      `uvm_create_on(sideload_seq, p_sequencer.key_sideload_sequencer_h);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(sideload_seq,
                                     sideload_key.valid == 1;)
      `uvm_send(sideload_seq)

      if (!en_app) begin
        // Write the SW key to the CSRs.
        write_key_shares();
      end

      if (cfg.enable_masking && entropy_mode == EntropyModeSw) begin
        provide_sw_entropy();
      end

      // Wait a few cycles to let the internal state settle in.
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));


      // Disable the scoreboard for the error injection test.
      cfg.en_scb = 0;
      // Trigger KMAC operation and invalidate the sideloading key in a parallel
      // thread.
      fork
          send_kmac_req();
          inject_error(app_fsm_path, key_valid_path, exp_kmac_err);
      join
      cfg.en_scb = 1;

      // Read out the digest and wait until sha3_idle is asserted.
      read_digest_chunk(KMAC_STATE_SHARE0_BASE, keccak_block_size, share0);
      read_digest_chunk(KMAC_STATE_SHARE1_BASE, keccak_block_size, share1);

      if(!en_app) begin
        issue_cmd(CmdDone);
      end

      csr_spinwait(.ptr(ral.status.sha3_idle), .exp_data(1'b1), .backdoor(1));
      csr_rd_check(.ptr(ral.status), .compare_value(ral.status.get_reset()));

      // Disable the sideloade key.
      cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(sideload_seq,
                                     sideload_key.valid == 0;)
      sideload_seq.start(p_sequencer.key_sideload_sequencer_h);
    end
  endtask

  // If application interface is enabled and selected to AppKeymgr, then it is a keymgr app
  // interface request.
  virtual function bit is_keymgr_app();
    return en_app && (app_mode == AppKeymgr);
  endfunction

endclass
