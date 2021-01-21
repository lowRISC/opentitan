// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_scoreboard extends cip_base_scoreboard #(
    .CFG_T(keymgr_env_cfg),
    .RAL_T(keymgr_reg_block),
    .COV_T(keymgr_env_cov)
  );
  `uvm_component_utils(keymgr_scoreboard)
  `define CREATE_CMP_STR(VAR) \
    str = $sformatf("%0s\n %0s act: 0x%0h, exp: 0x%0h", str, `"VAR`", act.``VAR, exp.``VAR);

  typedef struct packed {
    bit [keymgr_pkg::SwBindingWidth-1:0]   RomExtSecurityDescriptor;
    bit [keymgr_pkg::KeyWidth-1:0]         HardwareRevisionSecret;
    bit [keymgr_pkg::DevIdWidth-1:0]       DeviceIdentifier;
    bit [keymgr_pkg::HealthStateWidth-1:0] HealthMeasurement;
    bit [keymgr_pkg::KeyWidth-1:0]         DiversificationKey;
  } adv_creator_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [keymgr_pkg::AdvDataWidth-keymgr_pkg::KeyWidth-TL_DW*4-1:0]  unused;
    bit [3:0][TL_DW-1:0] SoftwareBinding;
    bit [keymgr_pkg::KeyWidth-1:0] OwnerRootSecret;
  } adv_owner_int_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [keymgr_pkg::AdvDataWidth-TL_DW*4-1:0]  unused;
    bit [3:0][TL_DW-1:0] SoftwareBinding;
  } adv_owner_data_t;

  typedef struct packed {
    bit [TL_DW-1:0]      KeyVersion;
    bit [3:0][TL_DW-1:0] Salt;
    keymgr_pkg::seed_t   KeyID;
    keymgr_pkg::seed_t   SoftwareExportConstant;
  } gen_out_data_t;

  typedef enum int {
    UpdateSwOut,
    UpdateHwOut,
    UpdateInternalKey,
    NotUpdate
  } update_result_e;

  // local variables
  keymgr_pkg::keymgr_working_state_e current_state;
  keymgr_pkg::keymgr_op_status_e     current_op_status;

  // HW internal key, used for OP in current state
  key_shares_t current_internal_key;

  // preserve value at TL read address phase and compare it at read data phase
  keymgr_pkg::keymgr_op_status_e     addr_phase_op_status;
  bit                                addr_phase_cfgen;
  keymgr_pkg::keymgr_working_state_e addr_phase_working_state;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(keymgr_kmac_item) req_fifo;
  uvm_tlm_analysis_fifo #(keymgr_kmac_item) rsp_fifo;

  // local queues to hold incoming packets pending comparison
  // store meaningful data, in non-working state, should not match to these data
  bit [keymgr_pkg::AdvDataWidth-1:0] adv_data_a_array[keymgr_pkg::keymgr_working_state_e];
  bit [keymgr_pkg::IdDataWidth-1:0]  id_data_a_array[keymgr_pkg::keymgr_working_state_e];
  bit [keymgr_pkg::GenDataWidth-1:0] sw_data_a_array[keymgr_pkg::keymgr_working_state_e];
  bit [keymgr_pkg::GenDataWidth-1:0] hw_data_a_array[keymgr_pkg::keymgr_working_state_e];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    req_fifo = new("req_fifo", this);
    rsp_fifo = new("rsp_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      forever begin
        keymgr_kmac_item item;
        req_fifo.get(item);
        process_kmac_data_req(item);
      end
      forever begin
        keymgr_kmac_item item;
        rsp_fifo.get(item);
        process_kmac_data_rsp(item);
      end
      forever begin
        wait(!cfg.under_reset);
        wait(cfg.keymgr_vif.keymgr_en != lc_ctrl_pkg::On);
        if (current_state != keymgr_pkg::StReset) wipe_hw_keys();
        wait(cfg.keymgr_vif.keymgr_en == lc_ctrl_pkg::On);
      end
    join_none
  endtask

  virtual function void process_kmac_data_req(keymgr_kmac_item item);
    keymgr_pkg::keymgr_ops_e op = get_operation();

    // there must be a OP which causes the KMAC data req
    `DV_CHECK_EQ(current_op_status, keymgr_pkg::OpWip)

    if (cfg.keymgr_vif.keymgr_en != lc_ctrl_pkg::On) return;

    case (op)
      keymgr_pkg::OpAdvance: begin
        case (current_state)
          keymgr_pkg::StInit: begin
            bit is_err = get_hw_invalid_input();

            compare_adv_creator_data(.exp_match(!is_err),
                                     .byte_data_q(item.byte_data_q));
            if (is_err) compare_invalid_data(item.byte_data_q);
          end
          keymgr_pkg::StCreatorRootKey: begin
            bit is_err = get_hw_invalid_input();

            compare_adv_owner_int_data(.exp_match(!is_err),
                                       .byte_data_q(item.byte_data_q));
            if (is_err) compare_invalid_data(item.byte_data_q);
          end
          keymgr_pkg::StOwnerIntKey: begin
            compare_adv_owner_data(item.byte_data_q);
          end
          keymgr_pkg::StOwnerKey, keymgr_pkg::StDisabled: begin
            compare_invalid_data(item.byte_data_q);
          end
          default: `uvm_error(`gfn, $sformatf("Unexpected current_state: %0d", current_state))
        endcase
      end
      keymgr_pkg::OpGenId: begin
        if (get_is_kmac_data_correct()) compare_id_data(item.byte_data_q);
        else                            compare_invalid_data(item.byte_data_q);
      end
      keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut: begin
        if (get_is_kmac_data_correct()) compare_gen_out_data(item.byte_data_q);
        else                            compare_invalid_data(item.byte_data_q);
      end
      keymgr_pkg::OpDisable: begin
        compare_invalid_data(item.byte_data_q);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
    endcase
  endfunction

  virtual function void process_kmac_data_rsp(keymgr_kmac_item item);
    update_result_e update_result = process_update_after_op_done();

    case (update_result)
      UpdateInternalKey: begin
        current_internal_key = {item.rsp_digest_share1, item.rsp_digest_share0};
        cfg.keymgr_vif.store_internal_key(current_internal_key, current_state);

        `uvm_info(`gfn, $sformatf("Update internal key 0x%0h for state %s", current_internal_key,
                                  current_state.name), UVM_MEDIUM)
      end
      UpdateSwOut: begin
        bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output;

        sw_share_output = {item.rsp_digest_share1, item.rsp_digest_share0};
        foreach (sw_share_output[i, j]) begin
          string csr_name = $sformatf("sw_share%0d_output_%0d", i, j);
          uvm_reg csr = ral.get_reg_by_name(csr_name);

          void'(csr.predict(.value(sw_share_output[i][j]), .kind(UVM_PREDICT_DIRECT)));
          `uvm_info(`gfn, $sformatf("Predict %0s = 0x%0h", csr_name, sw_share_output[i][j]),
                    UVM_MEDIUM)
        end
      end
      UpdateHwOut: begin
        key_shares_t key_shares = {item.rsp_digest_share1, item.rsp_digest_share0};
        bit good_key = (get_err_code() == 0);
        keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
            `gmv(ral.control.dest_sel));

        if (dest != keymgr_pkg::None) begin
          cfg.keymgr_vif.update_sideload_key(key_shares, current_state, dest, good_key);
          `uvm_info(`gfn, $sformatf("Update sideload key 0x%0h for %s", key_shares, dest.name),
                    UVM_MEDIUM)
        end
      end
      default: `uvm_info(`gfn, "KMAC result isn't updated to any output", UVM_MEDIUM)
    endcase

    // IntrOpDone occurs after every KDF
    void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
  endfunction

  // update current_state, current_op_status, err_code, alert and return update_result for updating
  // internal key, HW/SW output
  virtual function update_result_e process_update_after_op_done();
    update_result_e update_result;
    keymgr_pkg::keymgr_ops_e op = get_operation();
    bit is_err = (get_err_code() > 0);

    if (is_err) current_op_status <= keymgr_pkg::OpDoneFail;
    else        current_op_status <= keymgr_pkg::OpDoneSuccess;

    process_error_n_alert();

    case (current_state)
      keymgr_pkg::StInit, keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey,
          keymgr_pkg::StOwnerKey: begin

        case (op)
          keymgr_pkg::OpAdvance: begin
            if (!get_hw_invalid_input()) begin
              // if it's StOwnerKey, it advacens to OpDisable. Key is just random value
              if (current_state == keymgr_pkg::StOwnerKey) update_result = NotUpdate;
              else                                         update_result = UpdateInternalKey;

              current_state = get_next_state(current_state);
              // set sw_binding_en after advance OP
              void'(ral.sw_binding_en.predict(.value(1)));
            end
          end
          keymgr_pkg::OpDisable: begin
            update_result = UpdateInternalKey;
            current_state = keymgr_pkg::StDisabled;
          end
          keymgr_pkg::OpGenId, keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut: begin
            // If any error, no update for output
            if (is_err) begin
              update_result = NotUpdate;
            end else if (op == keymgr_pkg::OpGenHwOut) begin
              update_result = UpdateHwOut;
            end else begin
              update_result = UpdateSwOut;
            end
          end
          default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
        endcase
      end
      keymgr_pkg::StDisabled: begin
        case (op)
          keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable: begin
            update_result = NotUpdate;
          end
          keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenId: begin
            update_result = UpdateSwOut;
          end
          keymgr_pkg::OpGenHwOut: begin
            update_result = UpdateHwOut;
          end
          default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
        endcase
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected current_state: %0s", current_state.name))
    endcase

    return update_result;
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      // if OP WIP or keymgr_en=0, will clear cfgen and below csr can't be written
      if ((current_op_status == keymgr_pkg::OpWip || cfg.keymgr_vif.keymgr_en != lc_ctrl_pkg::On) &&
          csr.get_name() inside {"control", "key_version",
          "sw_binding_0", "sw_binding_1", "sw_binding_2", "sw_binding_3",
          "salt_0", "salt_1", "salt_2", "salt_3"}) begin
        `uvm_info(`gfn, $sformatf("Reg write to %0s is ignored due to cfgen=0", csr.get_name()),
                  UVM_MEDIUM)
        return;
      end else if (`gmv(ral.sw_binding_en) == 0 && csr.get_name() inside {"sw_binding_0",
               "sw_binding_1", "sw_binding_2", "sw_binding_3"}) begin
        return;
      end else begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        if (data_phase_read) begin
          bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
          bit [NumKeyMgrIntr-1:0] intr_exp = `gmv(ral.intr_state);

          foreach (intr_exp[i]) begin
            keymgr_intr_e intr = keymgr_intr_e'(i);

            `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & intr_exp[i]),
                           $sformatf("Interrupt_pin: %0s", intr.name));
          end
        end
      end
      "intr_enable, err_code": begin
        // no speical handle is needed
      end
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
          bit [NumKeyMgrIntr-1:0] intr_exp = `gmv(ral.intr_state) | item.a_data;

          void'(ral.intr_state.predict(.value(intr_exp)));
          if (cfg.en_cov) begin
            foreach (intr_exp[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
            end
          end
        end
      end
      "cfgen": begin
        // Check in this block
        do_read_check = 1'b0;

        // skip checking cfgen value when it's advance OP in Reset, as it's hard to know what exact
        // time OP will complete
        if (current_state != keymgr_pkg::StReset || current_op_status != keymgr_pkg::OpWip) begin
          if (addr_phase_read) begin
            addr_phase_cfgen = current_op_status != keymgr_pkg::OpWip &&
                               cfg.keymgr_vif.keymgr_en == lc_ctrl_pkg::On;
          end else if (data_phase_read) begin
            `DV_CHECK_EQ(item.d_data, addr_phase_cfgen)
          end
        end
      end
      "control": begin
        if (addr_phase_write) begin
          bit start = `gmv(ral.control.start);

          if (start) begin
            keymgr_pkg::keymgr_ops_e op = get_operation();
            current_op_status = keymgr_pkg::OpWip;

            `uvm_info(`gfn, $sformatf("At %s, %s is issued", current_state.name, op.name), UVM_LOW)

            // In StReset, OP doesn't trigger KDF, update result here for InvalidOp and update
            // status at `op_status`
            // For other states, update result after KDF is done at process_kmac_data_rsp
            case (current_state)
              keymgr_pkg::StReset: begin
                if (op == keymgr_pkg::OpAdvance) begin
                  current_internal_key = {cfg.keymgr_vif.otp_key.key_share1,
                                          cfg.keymgr_vif.otp_key.key_share0};
                  cfg.keymgr_vif.store_internal_key(current_internal_key, current_state);
                end else begin // !OpAdvance
                  current_op_status = keymgr_pkg::OpDoneFail;
                  // No KDF issued, done interrupt/alert is triggered in next cycle
                  void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
                  fork
                    begin
                      cfg.clk_rst_vif.wait_clks(1);
                      process_error_n_alert();
                    end
                  join_none
                end
                void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
              end
              default: begin // other than StReset and StDisabled
                bit good_key = get_is_kmac_key_correct();

                // update kmac key for check
                cfg.keymgr_vif.update_kdf_key(current_internal_key, current_state, good_key);
              end
            endcase
          end // start
        end // addr_phase_write
      end
      "working_state": begin
        // Check in this block
        do_read_check = 1'b0;

        if (addr_phase_read) begin
          addr_phase_working_state = current_state;
        end else if (data_phase_read) begin
          // scb can't predict when advance from stReset is done, as it's updated internally and no
          // output to indicate that, skip checking it
          if (current_state != keymgr_pkg::StReset || current_op_status != keymgr_pkg::OpWip) begin
            keymgr_pkg::keymgr_working_state_e act_state;

            `downcast(act_state, item.d_data)
            `DV_CHECK_EQ(act_state, addr_phase_working_state)
          end
        end
      end
      "op_status": begin
        // Check in this block
        do_read_check = 1'b0;

        if (addr_phase_write) begin
          // W1C
          `downcast(current_op_status, int'(current_op_status) & ~item.a_data);
        end else if (addr_phase_read) begin
          addr_phase_op_status = current_op_status;
        end else if (data_phase_read) begin
          if (current_state == keymgr_pkg::StReset) begin
            // when advance from StReset to StInit, we don't know how long it will take, it's ok
            // when status is WIP or success
            `DV_CHECK_EQ(item.d_data inside {current_op_status, keymgr_pkg::OpDoneSuccess}, 1)
            if (item.d_data == keymgr_pkg::OpDoneSuccess) begin
              current_op_status = keymgr_pkg::OpDoneSuccess;
              current_state = get_next_state(current_state);
              void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
            end
          end else begin
            `DV_CHECK_EQ(item.d_data, addr_phase_op_status)
          end
        end
      end
      default: begin
        if (!uvm_re_match("sw_share*", csr.get_name())) begin // sw_share
          // if keymgr isn't On, SW output should be entropy and not match to predict value
          if (data_phase_read && cfg.keymgr_vif.keymgr_en != lc_ctrl_pkg::On) begin
            if (item.d_data != 0) begin
              do_read_check = 1'b0;
              `DV_CHECK_NE(item.d_data, `gmv(csr))
            end
          end
        end else begin // Not sw_share
          // TODO
          do_read_check = 1'b0;
        end
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(item.d_data, `gmv(csr),
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function bit [TL_DW-1:0] get_current_max_version();
    case (current_state)
      keymgr_pkg::StCreatorRootKey: return `gmv(ral.max_creator_key_ver);
      keymgr_pkg::StOwnerIntKey:    return `gmv(ral.max_owner_int_key_ver);
      keymgr_pkg::StOwnerKey:       return `gmv(ral.max_owner_key_ver);
      default: `uvm_fatal(`gfn, $sformatf("unexpected state %s", current_state.name))
    endcase
  endfunction

  virtual function void process_error_n_alert();
    keymgr_pkg::keymgr_ops_e op = get_operation();
    bit [TL_DW-1:0] err = get_err_code();

    void'(ral.err_code.predict(err));

    if (err[keymgr_pkg::ErrInvalidOut] || err[keymgr_pkg::ErrInvalidCmd]) begin
      set_exp_alert("fault_err");
    end
    if (err[keymgr_pkg::ErrInvalidOp] || err[keymgr_pkg::ErrInvalidIn]) begin
      set_exp_alert("operation_err");
    end

    `uvm_info(`gfn, $sformatf("%s is issued and error code is 'b%0b", op.name, err), UVM_MEDIUM)
  endfunction

  virtual function bit [TL_DW-1:0] get_err_code();
    keymgr_pkg::keymgr_ops_e op = get_operation();
    bit [TL_DW-1:0]          err_code;

    err_code[keymgr_pkg::ErrInvalidIn] = get_hw_invalid_input();

    case (current_state)
      keymgr_pkg::StReset: begin
        if (op != keymgr_pkg::OpAdvance) begin
          err_code[keymgr_pkg::ErrInvalidOp] = 1;
        end
      end
      keymgr_pkg::StInit: begin
        if (!(op inside {keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable})) begin
          err_code[keymgr_pkg::ErrInvalidOp] = 1;
        end
      end
      keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey, keymgr_pkg::StOwnerKey: begin
        if (op inside {keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut} &&
            get_sw_invalid_input()) begin
          err_code[keymgr_pkg::ErrInvalidIn] = 1;
        end
      end
      keymgr_pkg::StDisabled: begin
        err_code[keymgr_pkg::ErrInvalidOp] = 1;
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected state %s", current_state.name))
    endcase
    return err_code;
  endfunction

  // HW invalid input checks as following
  // When an advance operation is invoked:
  //   The working state key is checked for all 0’s and all 1’s.
  //   During Initialized state, creator seed, device ID and health state data is checked for all
  //   0’s and all 1’s.
  //   During CreatorRootKey state, the owner seed is checked for all 0’s and all 1’s.
  //   During all other states, nothing is explicitly checked.
  // When a generate output key operation is invoked:
  //   The working state key is checked for all 0’s and all 1’s.
  virtual function bit get_hw_invalid_input();
    bit is_err;

    if (current_internal_key inside {0, '1}) begin
      is_err = 1;
    end

    if (get_operation() != keymgr_pkg::OpAdvance) return is_err;

    // TODO, expand all types of errors for adding coverage later
    case (current_state)
      keymgr_pkg::StInit: begin
        if (cfg.keymgr_vif.keymgr_div inside {0, '1}) begin
          is_err = 1;
        end

        if (cfg.keymgr_vif.otp_hw_cfg.data.device_id inside {0, '1}) begin
          is_err = 1;
        end

        if (cfg.keymgr_vif.otp_key.key_share0 inside {0, '1}) begin
          is_err = 1;
        end

        if (cfg.keymgr_vif.otp_key.key_share1 inside {0, '1}) begin
          is_err = 1;
        end

        if (cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::CreatorSeedIdx] inside {0, '1}) begin
          is_err = 1;
        end
      end
      keymgr_pkg::StCreatorRootKey: begin
        if (cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::OwnerSeedIdx] inside {0, '1}) begin
          is_err = 1;
        end
      end
      default: ;
    endcase
    return is_err;
  endfunction

  virtual function bit get_sw_invalid_input();
    return get_current_max_version() < `gmv(ral.key_version);
  endfunction

  // in normal operational states, invalid command etc lead to random data for gen-out OP
  virtual function bit get_is_kmac_data_correct();
    bit [TL_DW-1:0] err_code = get_err_code();
    keymgr_pkg::keymgr_ops_e op = get_operation();

    if (current_state inside {keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey,
                              keymgr_pkg::StOwnerKey}) begin
      return !(err_code[keymgr_pkg::ErrInvalidCmd] |
               err_code[keymgr_pkg::ErrInvalidOut] |
               err_code[keymgr_pkg::ErrInvalidIn]);
    end else begin
      return 0;
    end
  endfunction

  // Entering StDisable or invalid op leads to random key
  virtual function bit get_is_kmac_key_correct();
    bit [TL_DW-1:0] err_code = get_err_code();
    keymgr_pkg::keymgr_ops_e op = get_operation();

    if ((current_state == keymgr_pkg::StOwnerKey && op == keymgr_pkg::OpAdvance) ||
        op == keymgr_pkg::OpDisable) begin
      return 0;
    end else begin
      return !(err_code[keymgr_pkg::ErrInvalidOp]);
    end
  endfunction

  virtual function void compare_adv_creator_data(bit exp_match, const ref byte byte_data_q[$]);
    adv_creator_data_t exp, act;
    string str;

    if (exp_match) `DV_CHECK_EQ(byte_data_q.size, keymgr_pkg::AdvDataWidth / 8)
    act = {<<8{byte_data_q}};

    exp.DiversificationKey = cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::CreatorSeedIdx];
    exp.HealthMeasurement  = cfg.keymgr_vif.keymgr_div;
    exp.DeviceIdentifier   = cfg.keymgr_vif.otp_hw_cfg.data.device_id;
    exp.HardwareRevisionSecret = keymgr_pkg::RndCnstRevisionSeedDefault;
    exp.RomExtSecurityDescriptor = {`gmv(ral.sw_binding_3), `gmv(ral.sw_binding_2),
                                    `gmv(ral.sw_binding_1), `gmv(ral.sw_binding_0)};

    `CREATE_CMP_STR(DiversificationKey)
    `CREATE_CMP_STR(HealthMeasurement)
    `CREATE_CMP_STR(DeviceIdentifier)
    `CREATE_CMP_STR(HardwareRevisionSecret)
    `CREATE_CMP_STR(RomExtSecurityDescriptor)

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[keymgr_pkg::StCreatorRootKey] = act;
  endfunction

  virtual function void compare_adv_owner_int_data(bit exp_match, const ref byte byte_data_q[$]);
    adv_owner_int_data_t exp, act;
    string str;

    act = {<<8{byte_data_q}};

    exp.OwnerRootSecret = cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::OwnerSeedIdx];
    exp.SoftwareBinding[3] = `gmv(ral.sw_binding_3);
    exp.SoftwareBinding[2] = `gmv(ral.sw_binding_2);
    exp.SoftwareBinding[1] = `gmv(ral.sw_binding_1);
    exp.SoftwareBinding[0] = `gmv(ral.sw_binding_0);

    `CREATE_CMP_STR(unused)
    `CREATE_CMP_STR(OwnerRootSecret)
    `CREATE_CMP_STR(SoftwareBinding[3])
    `CREATE_CMP_STR(SoftwareBinding[2])
    `CREATE_CMP_STR(SoftwareBinding[1])
    `CREATE_CMP_STR(SoftwareBinding[0])

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[keymgr_pkg::StOwnerIntKey] = act;
  endfunction

  virtual function void compare_adv_owner_data(const ref byte byte_data_q[$]);
    adv_owner_data_t exp, act;
    string str;

    act = {<<8{byte_data_q}};

    exp.SoftwareBinding[3] = `gmv(ral.sw_binding_3);
    exp.SoftwareBinding[2] = `gmv(ral.sw_binding_2);
    exp.SoftwareBinding[1] = `gmv(ral.sw_binding_1);
    exp.SoftwareBinding[0] = `gmv(ral.sw_binding_0);

    `CREATE_CMP_STR(unused)
    `CREATE_CMP_STR(SoftwareBinding[3])
    `CREATE_CMP_STR(SoftwareBinding[2])
    `CREATE_CMP_STR(SoftwareBinding[1])
    `CREATE_CMP_STR(SoftwareBinding[0])

    `DV_CHECK_EQ(act, exp, str)

    adv_data_a_array[keymgr_pkg::StOwnerKey] = act;
  endfunction

  // for invalid OP, should not output any meaningful data to KMAC. Check the outputs aren't
  // matching to any of existing meaningful data
  virtual function void compare_invalid_data(const ref byte byte_data_q[$]);
    adv_owner_data_t act;

    act = {<<8{byte_data_q}};
    foreach (adv_data_a_array[i]) begin
      `DV_CHECK_NE(act, adv_data_a_array[i], $sformatf("Adv data to state %0s", i.name))
    end
    foreach (id_data_a_array[i]) begin
      `DV_CHECK_NE(act, id_data_a_array[i], $sformatf("ID data at state %0s", i.name))
    end
    foreach (sw_data_a_array[i]) begin
      `DV_CHECK_NE(act, sw_data_a_array[i], $sformatf("SW data at state %0s", i.name))
    end
    foreach (hw_data_a_array[i]) begin
      `DV_CHECK_NE(act, hw_data_a_array[i], $sformatf("HW data at state %0s", i.name))
    end
    foreach (cfg.keymgr_vif.keys_a_array[i, j]) begin
      `DV_CHECK_NE(act, cfg.keymgr_vif.keys_a_array[i][j],
                   $sformatf("key at state %0s from %0s", i, j))
    end
  endfunction

  virtual function void compare_id_data(const ref byte byte_data_q[$]);
    bit [keymgr_pkg::IdDataWidth-1:0] act, exp;

    case (current_state)
      keymgr_pkg::StCreatorRootKey: exp = keymgr_pkg::RndCnstCreatorIdentitySeedDefault;
      keymgr_pkg::StOwnerIntKey:    exp = keymgr_pkg::RndCnstOwnerIntIdentitySeedDefault;
      keymgr_pkg::StOwnerKey:       exp = keymgr_pkg::RndCnstOwnerIdentitySeedDefault;
      default: `uvm_fatal(`gfn, $sformatf("unexpected state %s", current_state.name))
    endcase
    act = {<<8{byte_data_q}};

    `DV_CHECK_EQ(act, exp, $sformatf("Gen ID at %0s", current_state.name))

    id_data_a_array[current_state] = act;
  endfunction

  virtual function void compare_gen_out_data(const ref byte byte_data_q[$]);
    gen_out_data_t exp, act;
    keymgr_pkg::keymgr_ops_e op = get_operation();
    keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
            `gmv(ral.control.dest_sel));
    string str;

    act = {<<8{byte_data_q}};

    exp.KeyVersion = `gmv(ral.key_version);
    exp.Salt[0]    = `gmv(ral.salt_0);
    exp.Salt[1]    = `gmv(ral.salt_1);
    exp.Salt[2]    = `gmv(ral.salt_2);
    exp.Salt[3]    = `gmv(ral.salt_3);
    case (dest)
      keymgr_pkg::Kmac: exp.KeyID = keymgr_pkg::RndCnstKmacSeedDefault;
      keymgr_pkg::Hmac: exp.KeyID = keymgr_pkg::RndCnstHmacSeedDefault;
      keymgr_pkg::Aes:  exp.KeyID = keymgr_pkg::RndCnstAesSeedDefault;
      keymgr_pkg::None: exp.KeyID = keymgr_pkg::RndCnstNoneSeedDefault;
      default: `uvm_fatal(`gfn, $sformatf("Unexpected dest_sel: %0s", dest.name))
    endcase

    case (op)
      keymgr_pkg::OpGenSwOut: begin
        exp.SoftwareExportConstant = keymgr_pkg::RndCnstSoftOutputSeedDefault;
        sw_data_a_array[current_state] = act;
      end
      keymgr_pkg::OpGenHwOut: begin
        exp.SoftwareExportConstant = keymgr_pkg::RndCnstHardOutputSeedDefault;
        hw_data_a_array[current_state] = act;
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
    endcase

    `CREATE_CMP_STR(KeyVersion)
    `CREATE_CMP_STR(Salt)
    `CREATE_CMP_STR(KeyID)
    `CREATE_CMP_STR(SoftwareExportConstant)

    `DV_CHECK_EQ(act, exp, str)
  endfunction

  // if it's not defined operation, treat as OpDisable
  virtual function keymgr_pkg::keymgr_ops_e get_operation();
    keymgr_pkg::keymgr_ops_e op;
    int op_int_val = `gmv(ral.control.operation);

    if (!$cast(op, op_int_val)) op = keymgr_pkg::OpDisable;
    return op;
  endfunction

  virtual function keymgr_pkg::keymgr_working_state_e get_next_state(keymgr_pkg::keymgr_working_state_e cur);
    if (cfg.keymgr_vif.keymgr_en != lc_ctrl_pkg::On) return keymgr_pkg::StInvalid;
    else                                             return keymgr_env_pkg::get_next_state(cur);
  endfunction

  // TODO, need designer to update for #4680
  virtual function void wipe_hw_keys();
    `uvm_info(`gfn, "Keymgr_en is Off, wipe secret and move state to Invalid", UVM_LOW)
    current_state = keymgr_pkg::StInvalid;
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    current_state     = keymgr_pkg::StReset;
    current_op_status = keymgr_pkg::OpIdle;
    current_internal_key = 0;
    adv_data_a_array.delete();
    id_data_a_array.delete();
    sw_data_a_array.delete();
    hw_data_a_array.delete();
    cfg.keymgr_vif.reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(keymgr_kmac_item, req_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(keymgr_kmac_item, rsp_fifo)
  endfunction

  `undef CREATE_CMP_STR
endclass
