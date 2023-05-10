// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class kmac_smoke_vseq extends kmac_base_vseq;

  `uvm_object_utils(kmac_smoke_vseq)
  `uvm_object_new

  bit kmac_done = 0;

  // Set this bit if we want to burst write the message into the msgfifo
  bit burst_write = 0;

  rand bit en_app;

  rand kmac_app_e app_mode;

  // Set this bit to one if entropy fetched successfully without timeout error.
  bit entropy_fetched;

  constraint num_trans_c {
    num_trans inside {[1:200]};
    if (cfg.smoke_test) {
      num_trans == 10;
    } else {
      num_trans inside {[1:200]};
    }
  }

  // If in KMAC mode, the function name has to be "KMAC" string
  constraint legal_fname_c {
    solve kmac_err_type before kmac_en;
    solve kmac_err_type before fname_arr;

    if (kmac_err_type != kmac_pkg::ErrIncorrectFunctionName) {
      if (kmac_en) {
        fname_len == 4;
        fname_arr[0] == 75; // "K"
        fname_arr[1] == 77; // "M"
        fname_arr[2] == 65; // "A"
        fname_arr[3] == 67; // "C"
      } else {
        fname_len == 0;
      }
    }
  }

  constraint disable_err_c {
    kmac_err_type == kmac_pkg::ErrNone;
  }

  constraint en_app_c {
    en_app == 0;
  }

  constraint custom_str_len_c {
    custom_str_len == 0;
  }

  constraint en_sideload_c {
    reg_en_sideload == 0;
  }

  constraint entropy_ready_c {
    entropy_ready == 1;
  }

  constraint entropy_refresh_c {
    hash_threshold == 0;
    hash_cnt_clr   == 0;
    entropy_req    == 0;
  }

  // Constraint output byte length to be at most the keccak block size (168/136).
  // This way we can read the entire digest without having to manually squeeze data.
  constraint output_len_c {
    output_len inside {[1:keccak_block_size]};
  }

  // for smoke test keep message below 32 bytes
  constraint msg_c {
    msg.size() dist {
      0      :/ 1,
      [1:32] :/ 9
    };
  }

  virtual function string convert2string();
    return {$sformatf("en_app: %0b\n", en_app),
            $sformatf("app_mode:%0s\n", app_mode.name()),
            super.convert2string()};
  endfunction

  // We want to disable do_kmac_init here because we wil re-initialize the KMAC each time we do
  // a message hash.
  virtual task pre_start();
    do_kmac_init = 0;
    super.pre_start();
  endtask

  // Do a full message hash, repeated num_trans times
  task body();

    logic [keymgr_pkg::KeyWidth-1:0] sideload_share0;
    logic [keymgr_pkg::KeyWidth-1:0] sideload_share1;
    key_sideload_set_seq sideload_seq;

    `uvm_info(`gfn, $sformatf("Starting %0d message hashes", num_trans), UVM_LOW)

    for (int i = 0; i < num_trans; i++) begin
      bit [7:0] share0[];
      bit [7:0] share1[];

      `uvm_info(`gfn, $sformatf("iteration: %0d", i), UVM_LOW)

      `DV_CHECK_RANDOMIZE_FATAL(this)

      kmac_init(.keymgr_app_intf(is_keymgr_app()));
      `uvm_info(`gfn, "kmac_init done", UVM_HIGH)

      read_regwen_and_rand_write_locked_regs();

      if (cfg.enable_masking && kmac_err_type == kmac_pkg::ErrWaitTimerExpired &&
          entropy_mode == EntropyModeEdn) begin
        if (entropy_fetched == 0) begin
          check_err();
          // Edn wait timer expired will lock entropy FSM, so the other operations cannot proceed
          // unless the entropy is provided.
          continue;
        end
      end else if (cfg.enable_masking && entropy_mode == EntropyModeEdn) begin
        entropy_fetched = 1;
      end

      if (cfg.enable_masking && kmac_err_type == kmac_pkg::ErrIncorrectEntropyMode) begin
        if (!entropy_fetched) begin
          check_err();
          continue;
        end
      end else if (cfg.enable_masking) begin
        entropy_fetched = 1;
      end

      set_prefix();

      // provide a random sideloaded key
      if (require_sideload_key()) begin
        `uvm_create_on(sideload_seq, p_sequencer.key_sideload_sequencer_h);
        `DV_CHECK_RANDOMIZE_WITH_FATAL(sideload_seq,
                                       sideload_key.valid ==
                                       (kmac_err_type != kmac_pkg::ErrKeyNotValid);)
        `uvm_send(sideload_seq)
      end

      if (kmac_en) begin
        // write the SW key to the CSRs
        if (!en_app) begin
          write_key_shares();
        end
      end

      if (cfg.enable_masking && entropy_mode == EntropyModeSw) begin
        `uvm_info(`gfn, "providing SW entropy", UVM_HIGH)
        provide_sw_entropy();
      end

      // Only send a KMAC_APP request when in KMAC mode
      if (en_app) begin
        bit process_key_err_before_app_done = $urandom_range(0, 1);
        // Inject error might be disabled by the `send_kmac_req` thread.
        bit error_injected = 0;

        `uvm_info(`gfn, $sformatf("process_key_err_before_app_done: %0b",
                  process_key_err_before_app_done), UVM_HIGH)
        fork
          // This thread carries out the "normal" functionality by initiating data transfer
          // over the application interface to the KMAC.
          //
          // We disable all error case subprocesses once the valid data transfer has finished as
          // to not cause spurious issues later on in the simulation.
          `uvm_info(`gfn, "starting kmac_app requests", UVM_HIGH)
          begin : send_kmac_req
            send_kmac_app_req(app_mode);
            wait_no_outstanding_access();
            disable invalid_msgfifo_wr;
            disable sw_cmd_in_app;
            disable check_invalid_key_err;
          end : send_kmac_req

          // This thread will create an error case by writing some data to the message FIFO
          // while an application interface operation is in progress.
          if (kmac_err_type == kmac_pkg::ErrSwPushedMsgFifo) begin : invalid_msgfifo_wr
            bit [TL_DW-1:0] rand_data;
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fifo_addr)
            `DV_CHECK_STD_RANDOMIZE_FATAL(rand_data)
            wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.valid);
            tl_access(.addr(ral.get_addr_from_offset(fifo_addr)),
                      .write(1),
                      .data(rand_data),
                      .mask(get_rand_contiguous_mask()),
                      .blocking(1));
            error_injected = 1;
          end : invalid_msgfifo_wr

          // This thread will create an error case by writing a SW command to the KMAC
          // while an application interface operation is in progress.
          //
          // As per designer comment on https://github.com/lowRISC/opentitan/issues/7716,
          // the only command that will trigger this particular error is CmdStart.
          if (kmac_err_type == kmac_pkg::ErrSwIssuedCmdInAppActive) begin : sw_cmd_in_app
            kmac_pkg::kmac_cmd_e invalid_cmd = kmac_pkg::CmdStart;
            wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.valid);
            cfg.clk_rst_vif.wait_clks($urandom_range(25, 250));
            issue_cmd(invalid_cmd);
            error_injected = 1;
          end : sw_cmd_in_app

          // This thread will create an error case by checking that an invalid key has been
          // provided to an AppKeymgr operation that is in progress.
          if (kmac_err_type == kmac_pkg::ErrKeyNotValid) begin : check_invalid_key_err
            // wait until the first valid request is seen
            wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.kmac_data_req.valid);
            if (process_key_err_before_app_done) begin
              disable send_kmac_req;
              check_err();
              // read the output window to ensure nothing has been corrupted
              read_digest_chunk(KMAC_STATE_SHARE0_BASE, keccak_block_size, share0);
              read_digest_chunk(KMAC_STATE_SHARE1_BASE, keccak_block_size, share1);
              csr_utils_pkg::wait_no_outstanding_access();
            end
            error_injected = 1;
          end : check_invalid_key_err
        join
        if (kmac_err_type != kmac_pkg::ErrNone && process_key_err_before_app_done) begin
          continue;
        end else begin
          // Wait until the KMAC engine has completely finished
          `uvm_info(`gfn, "waiting for kmac_app operation to finish", UVM_HIGH)
          wait (cfg.m_kmac_app_agent_cfg[app_mode].vif.rsp_done == 1);
          `uvm_info(`gfn, "finished waiting for kmac_app operation", UVM_HIGH)

          if (kmac_err_type inside
              {kmac_pkg::ErrSwPushedMsgFifo, kmac_pkg::ErrSwIssuedCmdInAppActive} &&
              error_injected) begin
            // For ErrSwPushedMsgFifo error, err_code.get_mirror_value method
            // incorrect return value for error injection test.
            // Skip read check to remove false error.
            cfg.skip_read_check = 1;
            check_err();
            cfg.skip_read_check = 0;
            csr_utils_pkg::wait_no_outstanding_access();
          end

          // If no error, wait a few cycles until Idle status is reflected to the status register.
          cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        end
      end else begin
        // normal hashing operation

        // issue an incorrect SW command, this will be dropped internally,
        // so need to send correct command afterwards.
        if (kmac_err_type == kmac_pkg::ErrSwCmdSequence &&
            err_sw_cmd_seq_st == sha3_pkg::StIdle) begin
          issue_cmd(err_sw_cmd_seq_cmd);
          check_err();
        end

        // issue Start cmd
        issue_cmd(CmdStart);

        read_regwen_and_rand_write_locked_regs();

        // write the message into msgfifo
        `uvm_info(`gfn, $sformatf("msg: %0p", msg), UVM_HIGH)
        if (burst_write) begin
          burst_write_msg(msg);
        end else begin
          write_msg(msg);
        end

        // if using KMAC, need to write either encoded output length or 0 to msgfifo
        if (kmac_en) begin
          right_encode(xof_en ? 0 : output_len * 8, output_len_enc);
          `uvm_info(`gfn, $sformatf("output_len_enc: %0p", output_len_enc), UVM_HIGH)
          write_msg(output_len_enc);
        end

        // wait for some cycles after writing message to let internal state settle
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));

        // issue an incorrect SW command, this will be dropped internally,
        // so need to send the correct command afterwards.
        if (kmac_err_type == kmac_pkg::ErrSwCmdSequence &&
            err_sw_cmd_seq_st == sha3_pkg::StAbsorb) begin
          issue_cmd(err_sw_cmd_seq_cmd);
          check_err();
        end

        // issue Process cmd
        issue_cmd(CmdProcess);

        if (kmac_err_type == kmac_pkg::ErrUnexpectedModeStrength &&
            en_unsupported_modestrength == 0) begin
          continue;
        end

        wait_for_kmac_done();
        kmac_done = 1;

        read_regwen_and_rand_write_locked_regs();
      end

      // read out intr_state and status, scb will check
      check_state();

      check_hash_cnt();

      // Read the output digest, scb will check digest
      //
      // If performing a KMAC_APP operation, digest will be sent directly to the m_kmac_app_agent,
      // so scoreboard will handle everything
      //
      read_digest_shares(output_len, cfg.enable_masking, share0, share1);

      if (!en_app) begin
        // issue an incorrect SW command, this will be dropped internally,
        // so need to send the correct command afterwards.
        if (kmac_err_type == kmac_pkg::ErrSwCmdSequence &&
            err_sw_cmd_seq_st == sha3_pkg::StSqueeze) begin
          issue_cmd(err_sw_cmd_seq_cmd);
          check_err();
        end

        // issue Done cmd to tell KMAC to clear internal state
        issue_cmd(CmdDone);
      end

      // randomly read out both digests after issuing Done cmd.
      if ($urandom_range(0, 1)) begin
        read_digest_chunk(KMAC_STATE_SHARE0_BASE, keccak_block_size, share0);
        read_digest_chunk(KMAC_STATE_SHARE1_BASE, keccak_block_size, share1);
      end else begin
        // If we don't read out the state window again, wait a few clocks before dropping the
        // sideload key (if applicable).
        cfg.clk_rst_vif.wait_clks(5);
      end

      // Drop the sideloaded key if it was provided to the DUT.
      if (require_sideload_key()) begin
        `uvm_info(`gfn, "dropping sideload key", UVM_HIGH)
        `DV_CHECK_RANDOMIZE_WITH_FATAL(sideload_seq,
                                       sideload_key.valid == 0;)
        sideload_seq.start(p_sequencer.key_sideload_sequencer_h);
      end

    end

  endtask : body

  virtual function bit require_sideload_key();
    return kmac_en && (reg_en_sideload || provide_sideload_key || is_keymgr_app());
  endfunction

  // If application interface is enabled and selected to AppKeymgr, then it is a keymgr app
  // interface request.
  virtual function bit is_keymgr_app();
    return en_app && (app_mode == AppKeymgr);
  endfunction
endclass : kmac_smoke_vseq
