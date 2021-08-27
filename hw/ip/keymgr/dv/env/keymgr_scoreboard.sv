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
    bit [keymgr_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] SoftwareBinding;
    bit [keymgr_pkg::KeyWidth-1:0]         HardwareRevisionSecret;
    bit [keymgr_pkg::DevIdWidth-1:0]       DeviceIdentifier;
    bit [keymgr_pkg::HealthStateWidth-1:0] HealthMeasurement;
    bit [keymgr_pkg::KeyWidth-1:0]         RomDigest;
    bit [keymgr_pkg::KeyWidth-1:0]         DiversificationKey;
  } adv_creator_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [keymgr_pkg::AdvDataWidth-keymgr_pkg::KeyWidth-keymgr_pkg::SwBindingWidth-1:0] unused;
    bit [keymgr_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] SoftwareBinding;
    bit [keymgr_pkg::KeyWidth-1:0] OwnerRootSecret;
  } adv_owner_int_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [keymgr_pkg::AdvDataWidth-keymgr_pkg::SwBindingWidth-1:0]  unused;
    bit [keymgr_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] SoftwareBinding;
  } adv_owner_data_t;

  typedef struct packed {
    bit [TL_DW-1:0]      KeyVersion;
    bit [keymgr_reg_pkg::NumSaltReg-1:0][TL_DW-1:0] Salt;
    keymgr_pkg::seed_t   KeyID;
    keymgr_pkg::seed_t   SoftwareExportConstant;
  } gen_out_data_t;

  typedef enum int {
    UpdateSwOut,
    UpdateHwOut,
    UpdateInternalKey,
    NotUpdate
  } update_result_e;

  int adv_cnt = 0;

  // local variables
  keymgr_pkg::keymgr_working_state_e current_state;
  keymgr_pkg::keymgr_op_status_e     current_op_status;
  bit                                is_kmac_rsp_err;
  bit                                is_kmac_invalid_data;
  bit                                invalid_status_err;
  bit                                is_sw_share_corrupted;

  // HW internal key, used for OP in current state
  key_shares_t current_internal_key[keymgr_cdi_type_e];
  keymgr_cdi_type_e current_cdi;

  // preserve value at TL read address phase and compare it at read data phase
  keymgr_pkg::keymgr_op_status_e     addr_phase_op_status;
  bit                                addr_phase_cfg_regwen;
  keymgr_pkg::keymgr_working_state_e addr_phase_working_state;
  bit                                addr_phase_is_sw_share_corrupted;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(kmac_app_item) req_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) rsp_fifo;

  // local queues to hold incoming packets pending comparison
  // store meaningful data, in non-working state, should not match to these data
  bit [keymgr_pkg::AdvDataWidth-1:0] adv_data_a_array[keymgr_cdi_type_e][
                                     keymgr_pkg::keymgr_working_state_e];
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
        kmac_app_item item;
        req_fifo.get(item);
        if (!cfg.en_scb) continue;
        process_kmac_data_req(item);
      end
      forever begin
        kmac_app_item item;
        rsp_fifo.get(item);
        if (!cfg.en_scb) continue;
        process_kmac_data_rsp(item);
      end
      forever begin
        wait(cfg.keymgr_vif.keymgr_en_sync2 != lc_ctrl_pkg::On);

        if (current_state != keymgr_pkg::StReset || current_op_status == keymgr_pkg::OpWip) begin
          wipe_hw_keys();
        end

        wait(cfg.keymgr_vif.keymgr_en_sync2 == lc_ctrl_pkg::On);
      end
    join_none
  endtask

  virtual function void process_kmac_data_req(kmac_app_item item);
    keymgr_pkg::keymgr_ops_e op = get_operation();


    if (!cfg.keymgr_vif.get_keymgr_en()) begin
      compare_invalid_data(item.byte_data_q);
      return;
    end else begin
      // there must be a OP which causes the KMAC data req
      `DV_CHECK_EQ(current_op_status, keymgr_pkg::OpWip)
    end

    case (op)
      keymgr_pkg::OpAdvance: begin

        case (current_state)
          keymgr_pkg::StInit: begin
            bit is_err = get_hw_invalid_input();
            compare_adv_creator_data(.cdi_type(current_cdi),
                                     .exp_match(!is_err),
                                     .byte_data_q(item.byte_data_q));
            if (is_err) compare_invalid_data(item.byte_data_q);
          end
          keymgr_pkg::StCreatorRootKey: begin
            bit is_err = get_hw_invalid_input();

            compare_adv_owner_int_data(.cdi_type(current_cdi),
                                       .exp_match(!is_err),
                                       .byte_data_q(item.byte_data_q));
            if (is_err) compare_invalid_data(item.byte_data_q);
          end
          keymgr_pkg::StOwnerIntKey: begin
            compare_adv_owner_data(current_cdi, item.byte_data_q);
          end
          keymgr_pkg::StOwnerKey, keymgr_pkg::StDisabled, keymgr_pkg::StInvalid: begin
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

  virtual function void process_kmac_data_rsp(kmac_app_item item);
    update_result_e update_result;
    bit process_update;

    is_kmac_rsp_err = item.rsp_error;
    is_kmac_invalid_data = item.get_is_kmac_rsp_data_invalid();
    update_result = process_update_after_op_done();

    case (update_result)
      UpdateInternalKey: begin
        // digest is 384 bits wide while internal key is only 256, need to truncate it
        current_internal_key[current_cdi] = {item.rsp_digest_share1[keymgr_pkg::KeyWidth-1:0],
                                             item.rsp_digest_share0[keymgr_pkg::KeyWidth-1:0]};
        cfg.keymgr_vif.store_internal_key(current_internal_key[current_cdi], current_state,
                                          current_cdi);

        `uvm_info(`gfn, $sformatf("Update internal key 0x%0h for state %s %s",
             current_internal_key[current_cdi], current_state.name, current_cdi.name), UVM_MEDIUM)
      end
      UpdateSwOut: begin
        if (!get_fault_err) begin
          bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output;
          // digest is 384 bits wide while SW output is only 256, need to truncate it
          sw_share_output = {item.rsp_digest_share1[keymgr_pkg::KeyWidth-1:0],
                             item.rsp_digest_share0[keymgr_pkg::KeyWidth-1:0]};
          foreach (sw_share_output[i, j]) begin
            string csr_name = $sformatf("sw_share%0d_output_%0d", i, j);
            uvm_reg csr = ral.get_reg_by_name(csr_name);

            void'(csr.predict(.value(sw_share_output[i][j]), .kind(UVM_PREDICT_DIRECT)));
            `uvm_info(`gfn, $sformatf("Predict %0s = 0x%0h", csr_name, sw_share_output[i][j]),
                      UVM_MEDIUM)
          end
        end
      end
      UpdateHwOut: begin
        kmac_digests_t key_shares = {item.rsp_digest_share1, item.rsp_digest_share0};
        keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
            `gmv(ral.control.dest_sel));

        if (dest != keymgr_pkg::None && !get_fault_err()) begin
          cfg.keymgr_vif.update_sideload_key(key_shares, current_state, current_cdi, dest);
          `uvm_info(`gfn, $sformatf("Update sideload key 0x%0h for %s", key_shares, dest.name),
                    UVM_MEDIUM)
        end
      end
      default: `uvm_info(`gfn, "KMAC result isn't updated to any output", UVM_MEDIUM)
    endcase

    if (!(current_state inside {keymgr_pkg::StReset, keymgr_pkg::StInvalid}) &&
        get_operation() inside {keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable}) begin
      current_cdi = get_adv_cdi_type();
      if (current_cdi > 0) begin
        cfg.keymgr_vif.update_kdf_key(current_internal_key[current_cdi], current_state,
                                      get_is_kmac_key_correct());
      end
    end
  endfunction

  // update current_state, current_op_status, err_code, alert and return update_result for updating
  // internal key, HW/SW output
  virtual function update_result_e process_update_after_op_done();
    update_result_e update_result;
    keymgr_pkg::keymgr_ops_e op = get_operation();
    bit is_final_kdf;

    // for advance after StReset, it needs 2 KDF. Only update opt_status after the last one
    if (!(op inside {keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable}) ||
        current_state == keymgr_pkg::StReset) begin
      is_final_kdf = 1;
    end else begin
      is_final_kdf = (adv_cnt == keymgr_pkg::CDIs - 1);
    end
    // op_status is updated one cycle after done. If SW reads at this edge, still return old value
    // delay half cycle to push the update available in next cycle
    fork
      begin
        cfg.clk_rst_vif.wait_n_clks(1);
        if (is_final_kdf) begin
          if (get_err_code()) current_op_status = keymgr_pkg::OpDoneFail;
          else                current_op_status = keymgr_pkg::OpDoneSuccess;
        end
      end
    join_none

    if (is_final_kdf && cfg.keymgr_vif.get_keymgr_en()) process_error_n_alert();
    // IntrOpDone occurs after every KDF
    void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));

    case (current_state)
      keymgr_pkg::StInit, keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey,
          keymgr_pkg::StOwnerKey: begin

        case (op)
          keymgr_pkg::OpAdvance: begin
            // if it's StOwnerKey, it advacens to OpDisable. Key is just random value
            if (current_state == keymgr_pkg::StOwnerKey || get_fault_err()) begin
              if (get_fault_err()) current_state = keymgr_pkg::StDisabled;
              update_result = NotUpdate;
            end else begin
              update_result = UpdateInternalKey;
            end

            if (adv_cnt != keymgr_pkg::CDIs - 1) begin
              adv_cnt++;
            end else begin
              adv_cnt = 0;
              update_state(get_next_state(current_state));
              // set sw_binding_regwen after advance OP
              void'(ral.sw_binding_regwen.predict(.value(1)));
              ral.sw_binding_regwen.en.set_lockable_flds_access(.lock(0));
            end
          end
          keymgr_pkg::OpDisable: begin
            update_result = UpdateInternalKey;
            if (adv_cnt != keymgr_pkg::CDIs - 1) begin
              adv_cnt++;
            end else begin
              adv_cnt = 0;
              update_state(keymgr_pkg::StDisabled);
            end
          end
          keymgr_pkg::OpGenId, keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut: begin
            // If only op error but no fault error, no update for output
            if (get_op_err() && !get_fault_err()) begin
              update_result = NotUpdate;
            end else if (op == keymgr_pkg::OpGenHwOut) begin
              update_result = UpdateHwOut;
            end else begin
              update_result = UpdateSwOut;
            end
            if (get_fault_err()) update_state(keymgr_pkg::StDisabled);
          end
          default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
        endcase
      end
      keymgr_pkg::StDisabled, keymgr_pkg::StInvalid: begin
        case (op)
          keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable: begin
            update_result = NotUpdate;
            if (adv_cnt != keymgr_pkg::CDIs - 1) begin
              adv_cnt++;
            end else begin
              adv_cnt = 0;
            end
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

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    dv_base_reg dv_reg;
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(dv_reg, csr)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      // if OP WIP or keymgr_en=0, will clear cfg_regwen and below csr can't be written
      if ((current_op_status == keymgr_pkg::OpWip || !cfg.keymgr_vif.get_keymgr_en()) &&
          ral.cfg_regwen.locks_reg_or_fld(dv_reg)) begin
        `uvm_info(`gfn, $sformatf("Reg write to %0s is ignored due to cfg_regwen=0", csr.get_name()),
                  UVM_MEDIUM)
        return;
      end else if (`gmv(ral.sw_binding_regwen) == 0 &&
          ral.sw_binding_regwen.locks_reg_or_fld(dv_reg)) begin
        `uvm_info(`gfn, $sformatf("Reg write to %0s is ignored due to sw_binding_regwen=0",
                                  csr.get_name()), UVM_MEDIUM)
        return;
      end else if (csr.get_name() == "sw_binding_regwen" && current_state == keymgr_pkg::StReset)
      begin
        `uvm_info(`gfn, $sformatf("Reg write to %0s is ignored due to state in StReset",
                                  csr.get_name()), UVM_MEDIUM)
        return;
      end else begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    if (data_phase_write && csr.get_name() == "sw_binding_regwen" &&
        current_state == keymgr_pkg::StReset) begin
      // in StReset, can't change sw_binding_regwen value
      // set related locked reg back to original_access as this is updated automatic in post_write
      #0; // push below update to be done after post_write
      ral.sw_binding_regwen.en.set_lockable_flds_access(.lock(0));
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
      "intr_enable", "err_code", "sw_binding_regwen": begin
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
      "cfg_regwen": begin
        // Check in this block
        do_read_check = 1'b0;

        // skip checking cfg_regwen value when it's advance OP in Reset, as it's hard to know what exact
        // time OP will complete
        if (current_state != keymgr_pkg::StReset || current_op_status != keymgr_pkg::OpWip) begin
          if (addr_phase_read) begin
            addr_phase_cfg_regwen = current_op_status != keymgr_pkg::OpWip &&
                               cfg.keymgr_vif.get_keymgr_en();
          end else if (data_phase_read) begin
            `DV_CHECK_EQ(item.d_data, addr_phase_cfg_regwen)
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
                  // for advance to OwnerRootSecret, both KDF use same otp_key
                  current_internal_key[Sealing] = {cfg.keymgr_vif.otp_key.key_share1,
                                                   cfg.keymgr_vif.otp_key.key_share0};
                  current_internal_key[Attestation] = current_internal_key[Sealing];
                  cfg.keymgr_vif.store_internal_key(current_internal_key[Sealing], current_state,
                                                    current_cdi);

                  // expect no EDN request is issued. After this advance is done, will have 2 reqs
                  `DV_CHECK_EQ(edn_fifo.is_empty(), 1)
                end else begin // !OpAdvance
                  current_op_status = keymgr_pkg::OpDoneFail;
                  // No KDF issued, done interrupt/alert is triggered in next cycle
                  void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
                  if (cfg.keymgr_vif.get_keymgr_en()) fork
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
                bit skip_clean_kmac_key = 0;

                if (current_state != keymgr_pkg::StReset &&
                    op inside {keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable}) begin
                  skip_clean_kmac_key = 1;
                end

                if (op == keymgr_pkg::OpAdvance) begin
                  current_cdi = get_adv_cdi_type();
                end else begin
                  int cdi_sel = `gmv(ral.control.cdi_sel);
                  `downcast(current_cdi, cdi_sel)
                end
                // update kmac key for check
                cfg.keymgr_vif.update_kdf_key(current_internal_key[current_cdi], current_state,
                                              good_key);
              end
            endcase
            // start will be clear after OP is done
            void'(ral.control.start.predict(.value(0), .kind(UVM_PREDICT_WRITE)));
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

              // keymgr should request 2 EDN data during advancing from StReset
              // function `used` returns the number of entries put into the FIFO
              `DV_CHECK_EQ(edn_fifo.used(), 2)
            end
          end else begin
            `DV_CHECK_EQ(item.d_data, addr_phase_op_status)
          end
        end
      end
      "reseed_interval_shadowed": begin
        if (addr_phase_write) cfg.keymgr_vif.edn_interval = `gmv(ral.reseed_interval_shadowed.val);
      end
      "sideload_clear": begin
        if (addr_phase_write) begin
          fork
            begin
              cfg.clk_rst_vif.wait_clks(1);
              cfg.keymgr_vif.clear_sideload_key(`gmv(ral.sideload_clear.val));
            end
          join_none
        end
      end
      default: begin
        if (!uvm_re_match("sw_share*", csr.get_name())) begin // sw_share
          // if keymgr isn't On, SW output should be entropy and not match to predict value
          if (addr_phase_read) begin
            addr_phase_is_sw_share_corrupted = is_sw_share_corrupted;
          end else if (data_phase_read && addr_phase_is_sw_share_corrupted) begin
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
      keymgr_pkg::StCreatorRootKey: return `gmv(ral.max_creator_key_ver_shadowed);
      keymgr_pkg::StOwnerIntKey:    return `gmv(ral.max_owner_int_key_ver_shadowed);
      keymgr_pkg::StOwnerKey:       return `gmv(ral.max_owner_key_ver_shadowed);
      // for the other state, max is 0
      default: return 0;
    endcase
  endfunction

  virtual function void process_error_n_alert();
    bit [TL_DW-1:0] err = get_err_code();
    void'(ral.err_code.predict(err));

    if (get_fault_err()) begin
      set_exp_alert("fatal_fault_err", .is_fatal(1));
      is_sw_share_corrupted = 1;
      cfg.keymgr_vif.wipe_sideload_keys();
    end
    if (get_op_err()) set_exp_alert("recov_operation_err");

    `uvm_info(`gfn, $sformatf("at %s, %s is issued and error code is 'b%0b",
              current_state, get_operation(), err), UVM_MEDIUM)
  endfunction

  virtual function bit [TL_DW-1:0] get_fault_err();
    bit [TL_DW-1:0] err = get_err_code();
    return err[keymgr_pkg::ErrInvalidStates];
  endfunction

  virtual function bit [TL_DW-1:0] get_op_err();
    bit [TL_DW-1:0] err = get_err_code();
    return err[keymgr_pkg::ErrInvalidOp] || err[keymgr_pkg::ErrInvalidIn];
  endfunction

  virtual function bit [TL_DW-1:0] get_err_code();
    bit [TL_DW-1:0] err_code;

    // TODO, clean up later
    // if keymgr_en is off during an OP, suppress op err
    //if (cfg.keymgr_vif.get_keymgr_en() && current_state != keymgr_pkg::StInvalid) begin
      err_code[keymgr_pkg::ErrInvalidOp]  = get_op_error();
    //end

    // this fault error is sticky, should preserve the value until reset
    if (!invalid_status_err) invalid_status_err = is_kmac_rsp_err | is_kmac_invalid_data;
    err_code[keymgr_pkg::ErrInvalidStates] = invalid_status_err;

    if (cfg.keymgr_vif.keymgr_en_sync2 == lc_ctrl_pkg::On) begin
      err_code[keymgr_pkg::ErrInvalidIn]  = get_hw_invalid_input() | get_sw_invalid_input();
    end

    `uvm_info(`gfn, $sformatf({"op_err = %0d, rsp_err = %0d, hw_invalid = %0d, sw_invalid = %0d, ",
              "kmac_invalid_data = %0d"},
              get_op_error(), is_kmac_rsp_err, get_hw_invalid_input(), get_sw_invalid_input(),
              is_kmac_invalid_data), UVM_MEDIUM)
    return err_code;
  endfunction

  virtual function bit get_op_error();
    `uvm_info(`gfn, $sformatf("current_state: %s", current_state), UVM_MEDIUM)
    case (current_state)
      keymgr_pkg::StReset: begin
        if (get_operation() != keymgr_pkg::OpAdvance) begin
          return 1;
        end
      end
      keymgr_pkg::StInit: begin
        if (!(get_operation() inside {keymgr_pkg::OpAdvance, keymgr_pkg::OpDisable})) begin
          return 1;
        end
      end
      keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey, keymgr_pkg::StOwnerKey: begin
        // no operation error
      end
      keymgr_pkg::StDisabled, keymgr_pkg::StInvalid: begin
        return 1;
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected state %s", current_state.name))
    endcase
    return 0;
  endfunction

  virtual function bit get_sw_invalid_input();
    if (get_operation() inside {keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut}) begin
      return get_current_max_version() < `gmv(ral.key_version[0]);
    end else begin
      return 0;
    end
  endfunction

  // HW invalid input checks as following
  // When an advance operation is invoked:
  //   The working state key is checked for all 0's and all 1's.
  //   During Initialized state, creator seed, device ID and health state data is checked for all
  //   0's and all 1's.
  //   During CreatorRootKey state, the owner seed is checked for all 0's and all 1's.
  //   During all other states, nothing is explicitly checked.
  // When a generate output key operation is invoked:
  //   The working state key is checked for all 0's and all 1's.
  virtual function bit get_hw_invalid_input();
    bit is_err;

    if (current_internal_key[current_cdi] inside {0, '1} && current_state != keymgr_pkg::StReset)
    begin
      is_err = 1;
      `uvm_info(`gfn, $sformatf("internal key for %s %s is invalid", current_state, current_cdi),
                UVM_LOW)
    end

    if (get_operation() != keymgr_pkg::OpAdvance) return is_err;

    // TODO, expand all types of errors for adding coverage later
    case (current_state)
      keymgr_pkg::StInit: begin
        if (cfg.keymgr_vif.keymgr_div inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on keymgr_div", UVM_LOW)
        end

        if (cfg.keymgr_vif.otp_device_id inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on otp_device_id", UVM_LOW)
        end

        if (cfg.keymgr_vif.rom_digest.data inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on rom_digest", UVM_LOW)
        end

        if (cfg.keymgr_vif.otp_key.key_share0 inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on key_share0", UVM_LOW)
        end

        if (cfg.keymgr_vif.otp_key.key_share1 inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on key_share1", UVM_LOW)
        end

        if (cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::CreatorSeedIdx] inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on flash.seeds[CreatorSeedIdx]", UVM_LOW)
        end
      end
      keymgr_pkg::StCreatorRootKey: begin
        if (cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::OwnerSeedIdx] inside {0, '1}) begin
          is_err = 1;
          `uvm_info(`gfn, "HW invalid input on flash.seeds[OwnerSeedIdx]", UVM_LOW)
        end
      end
      default: ;
    endcase
    return is_err;
  endfunction

  // in normal operational states, invalid command etc lead to random data for gen-out OP
  virtual function bit get_is_kmac_data_correct();
    bit [TL_DW-1:0] err_code = get_err_code();
    keymgr_pkg::keymgr_ops_e op = get_operation();

    if (current_state inside {keymgr_pkg::StCreatorRootKey, keymgr_pkg::StOwnerIntKey,
                              keymgr_pkg::StOwnerKey}) begin
      return !(err_code[keymgr_pkg::ErrInvalidStates] |
               err_code[keymgr_pkg::ErrInvalidIn]  |
               !cfg.keymgr_vif.get_keymgr_en());
    end else begin
      return 0;
    end
  endfunction

  // Entering StDisable or invalid op leads to random key
  virtual function bit get_is_kmac_key_correct();
    bit [TL_DW-1:0] err_code = get_err_code();
    keymgr_pkg::keymgr_ops_e op = get_operation();

    if ((current_state == keymgr_pkg::StOwnerKey && op == keymgr_pkg::OpAdvance) ||
        op == keymgr_pkg::OpDisable || !cfg.keymgr_vif.get_keymgr_en()) begin
      return 0;
    end else begin
      return !(err_code[keymgr_pkg::ErrInvalidOp]);
    end
  endfunction

  virtual function void compare_adv_creator_data(keymgr_cdi_type_e cdi_type,
                                                 bit exp_match,
                                                 const ref byte byte_data_q[$]);
    adv_creator_data_t exp, act;
    string str = $sformatf("cdi_type: %s\n", cdi_type.name);

    if (exp_match) `DV_CHECK_EQ(byte_data_q.size, keymgr_pkg::AdvDataWidth / 8)
    act = {<<8{byte_data_q}};

    exp.DiversificationKey = cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::CreatorSeedIdx];
    exp.RomDigest          = cfg.keymgr_vif.rom_digest.data;
    exp.HealthMeasurement  = cfg.keymgr_vif.keymgr_div;
    exp.DeviceIdentifier   = cfg.keymgr_vif.otp_device_id;
    exp.HardwareRevisionSecret = keymgr_pkg::RndCnstRevisionSeedDefault;

    get_sw_binding_mirrored_value(cdi_type, exp.SoftwareBinding);

    // The order of the string creation must match the design
    `CREATE_CMP_STR(DiversificationKey)
    `CREATE_CMP_STR(RomDigest)
    `CREATE_CMP_STR(HealthMeasurement)
    `CREATE_CMP_STR(DeviceIdentifier)
    `CREATE_CMP_STR(HardwareRevisionSecret)
    `CREATE_CMP_STR(SoftwareBinding)

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[Sealing][keymgr_pkg::StCreatorRootKey] = act;
  endfunction

  virtual function void compare_adv_owner_int_data(keymgr_cdi_type_e cdi_type,
                                                   bit exp_match,
                                                   const ref byte byte_data_q[$]);
    adv_owner_int_data_t exp, act;
    string str = $sformatf("cdi_type: %s\n", cdi_type.name);

    act = {<<8{byte_data_q}};

    exp.OwnerRootSecret = cfg.keymgr_vif.flash.seeds[flash_ctrl_pkg::OwnerSeedIdx];
    get_sw_binding_mirrored_value(cdi_type, exp.SoftwareBinding);

    `CREATE_CMP_STR(unused)
    `CREATE_CMP_STR(OwnerRootSecret)
    for (int i=0; i < keymgr_reg_pkg::NumSwBindingReg; i++) begin
      `CREATE_CMP_STR(SoftwareBinding[i])
    end

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[Sealing][keymgr_pkg::StOwnerIntKey] = act;
  endfunction

  virtual function void compare_adv_owner_data(keymgr_cdi_type_e cdi_type,
                                               const ref byte byte_data_q[$]);
    adv_owner_data_t exp, act;
    string str = $sformatf("cdi_type: %s\n", cdi_type.name);

    act = {<<8{byte_data_q}};

    get_sw_binding_mirrored_value(cdi_type, exp.SoftwareBinding);

    `CREATE_CMP_STR(unused)
    for (int i=0; i < keymgr_reg_pkg::NumSwBindingReg; i++) begin
      `CREATE_CMP_STR(SoftwareBinding[i])
    end

    `DV_CHECK_EQ(act, exp, str)

    adv_data_a_array[Sealing][keymgr_pkg::StOwnerKey] = act;
  endfunction

  // for invalid OP, should not output any meaningful data to KMAC. Check the outputs aren't
  // matching to any of existing meaningful data
  virtual function void compare_invalid_data(const ref byte byte_data_q[$]);
    adv_owner_data_t act;

    act = {<<8{byte_data_q}};
    foreach (adv_data_a_array[i, j]) begin
      `DV_CHECK_NE(act, adv_data_a_array[i][j], $sformatf("Adv data to state %0s for %0s", j.name,
                                                          i.name))
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
    foreach (cfg.keymgr_vif.keys_a_array[state, cdi, dest]) begin
      `DV_CHECK_NE(act, cfg.keymgr_vif.keys_a_array[state][cdi][dest],
                   $sformatf("key at state %0s for %s %s", state.name, cdi.name, dest))
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

    exp.KeyVersion = `gmv(ral.key_version[0]);
    for (int i = 0; i < keymgr_reg_pkg::NumSaltReg; i++) begin
      uvm_reg rg = ral.get_reg_by_name($sformatf("salt_%0d", i));
      exp.Salt[i] = `gmv(rg);
    end

    case (dest)
      keymgr_pkg::Kmac: exp.KeyID = keymgr_pkg::RndCnstKmacSeedDefault;
      keymgr_pkg::Aes:  exp.KeyID = keymgr_pkg::RndCnstAesSeedDefault;
      keymgr_pkg::Otbn: exp.KeyID = keymgr_pkg::RndCnstOtbnSeedDefault;
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

  virtual function keymgr_cdi_type_e get_adv_cdi_type();
    `downcast(get_adv_cdi_type, adv_cnt)
  endfunction

  virtual function void get_sw_binding_mirrored_value(
        input keymgr_cdi_type_e cdi_type,
        output bit [keymgr_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] sw_binding);

    for (int i = 0; i < keymgr_reg_pkg::NumSwBindingReg; i++) begin
      case (cdi_type)
        Sealing: sw_binding[i] = `gmv(ral.sealing_sw_binding[i]);
        Attestation: sw_binding[i] = `gmv(ral.attest_sw_binding[i]);
        default: `uvm_fatal(`gfn, $sformatf("Unsupported CDI type %s", cdi_type.name))
      endcase
    end
  endfunction

  // if it's not defined operation, treat as OpDisable
  virtual function keymgr_pkg::keymgr_ops_e get_operation();
    keymgr_pkg::keymgr_ops_e op;
    int op_int_val = `gmv(ral.control.operation);

    if (!$cast(op, op_int_val)) op = keymgr_pkg::OpDisable;
    return op;
  endfunction

  virtual function keymgr_pkg::keymgr_working_state_e get_next_state(keymgr_pkg::keymgr_working_state_e cur);
    if (!cfg.keymgr_vif.get_keymgr_en()) return keymgr_pkg::StInvalid;
    else                                 return keymgr_env_pkg::get_next_state(cur);
  endfunction

  virtual function void update_state(keymgr_pkg::keymgr_working_state_e new_state, int cyc_dly = 1);
    fork
      begin
        // it takes 1 cycle to update state after rsp_done is set. add one more negedge to avoid
        // race condition
        cfg.clk_rst_vif.wait_n_clks(cyc_dly + 1);
        current_state = new_state;
      end
    join_none
  endfunction

  virtual function void wipe_hw_keys();
    if (current_op_status != keymgr_pkg::OpWip) begin
      // design takes 2 cycle to update state
      update_state(keymgr_pkg::StInvalid, .cyc_dly(2));
      `uvm_info(`gfn, "Keymgr_en is Off, wipe secret and move state to Invalid", UVM_LOW)
      cfg.keymgr_vif.wipe_sideload_keys();
    end
    fork
      begin
        if (current_op_status == keymgr_pkg::OpWip) begin
          // if operation is ongoing, then we must wait for response to be received
          // before transitioning
          wait(cfg.keymgr_vif.kmac_data_rsp.done);
          current_state = keymgr_pkg::StInvalid;
          `uvm_info(`gfn, "operation WIP but Keymgr_en is Off, update err_code and move to Invalid",
                    UVM_LOW)
          process_error_n_alert();
          current_op_status = keymgr_pkg::OpDoneFail;
        end else begin
          // it takes 2 cycle to wipe sw_share. add one more negedge to avoid race condition
          // corner case, keymgr_en is changed while OP is almost done. OP will finish successfully
          // delay update_state in 1 cycle
          cfg.clk_rst_vif.wait_n_clks(3);
          update_state(keymgr_pkg::StInvalid);
          `uvm_info(`gfn, "operation WIP but Keymgr_en is Off, move to Invalid", UVM_LOW)
        end
        is_sw_share_corrupted = 1;
        cfg.keymgr_vif.wipe_sideload_keys();
      end
    join_none
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    current_state         = keymgr_pkg::StReset;
    current_op_status     = keymgr_pkg::OpIdle;
    is_kmac_rsp_err       = 0;
    is_kmac_invalid_data  = 0;
    invalid_status_err    = 0;
    is_sw_share_corrupted = 0;
    req_fifo.flush();
    rsp_fifo.flush();
    current_internal_key.delete;
    adv_data_a_array.delete();
    id_data_a_array.delete();
    sw_data_a_array.delete();
    hw_data_a_array.delete();
    cfg.keymgr_vif.reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(kmac_app_item, req_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(kmac_app_item, rsp_fifo)
  endfunction

  `undef CREATE_CMP_STR
endclass
