// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_scoreboard extends cip_base_scoreboard #(
    .CFG_T(keymgr_dpe_env_cfg),
    .RAL_T(keymgr_dpe_reg_block),
    .COV_T(keymgr_dpe_env_cov)
  );
  `uvm_component_utils(keymgr_dpe_scoreboard)
  `define CREATE_CMP_STR(VAR) \
    str = $sformatf("%0s\n %0s act: 0x%0h, exp: 0x%0h", str, `"VAR`", act.``VAR, exp.``VAR);

  // if boot_stage == 0
  typedef struct packed {
    // SW_CDI_INPUT
    bit [keymgr_dpe_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0]               SoftwareBinding;
    // HW_REVISION_SEED 
    bit [keymgr_pkg::KeyWidth-1:0]                                         HardwareRevisionSecret;
    // DEVICE_IDENTIFIER
    bit [keymgr_pkg::DevIdWidth-1:0]                                       DeviceIdentifier;
    // HEALTH_ST_MEASUREMENT 
    bit [keymgr_pkg::HealthStateWidth-1:0]                                 HealthMeasurement;
    // ROM_DESCRIPTORS
    bit [keymgr_dpe_reg_pkg::NumRomDigestInputs-1:0][keymgr_pkg::KeyWidth-1:0] RomDigests;
    // CREATOR_SEED 
    bit [keymgr_pkg::KeyWidth-1:0]                                         DiversificationKey;
  } adv_creator_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [keymgr_pkg::AdvDataWidth-keymgr_pkg::KeyWidth-keymgr_pkg::SwBindingWidth-1:0] unused;
    // SW_CDI_INPUT
    bit [keymgr_dpe_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] SoftwareBinding;
    // OWNER SEED
    bit [keymgr_pkg::KeyWidth-1:0] OwnerRootSecret;
  } adv_owner_int_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [keymgr_pkg::AdvDataWidth-keymgr_pkg::SwBindingWidth-1:0]  unused;
    // SW_CDI_INPUT
    bit [keymgr_dpe_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] SoftwareBinding;
  } adv_owner_data_t;

  typedef struct packed {
    bit [TL_DW-1:0]      KeyVersion;
    bit [keymgr_dpe_reg_pkg::NumSaltReg-1:0][TL_DW-1:0] Salt;
    keymgr_pkg::seed_t   KeyID;
    keymgr_pkg::seed_t   SoftwareExportConstant;
  } gen_out_data_t;

  typedef enum int {
    UpdateSwOut,
    UpdateHwOut,
    UpdateInternalKey,
    NotUpdate
  } update_result_e;

  localparam int RESET_ADV_CYCLES = 2000;

  int adv_cnt = 0;

  // local variables
  keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e current_state;
  keymgr_pkg::keymgr_op_status_e     current_op_status;
  bit                                is_kmac_rsp_err;
  bit                                is_kmac_invalid_data;
  bit                                is_sw_share_corrupted;

  // HW internal key, used for OP in current state
  keymgr_dpe_env_pkg::keymgr_dpe_key_slot_t current_key_slot;
  keymgr_dpe_pkg::keymgr_dpe_slot_t current_internal_key[
	keymgr_dpe_pkg::DpeNumSlots];
  // bit used to flag a comparison of key slot is required
  // it's set by the process_kmac_data_rsp() function, during an
  // internal key update
  bit compare_internal_key_slot;
  keymgr_dpe_cdi_type_e current_cdi;

  // preserve value at TL read address phase and compare it at read data phase
  keymgr_pkg::keymgr_op_status_e     addr_phase_op_status;
  bit                                addr_phase_cfg_regwen;
  keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e addr_phase_working_state;
  bit                                addr_phase_is_sw_share_corrupted;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(kmac_app_item) req_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) rsp_fifo;

  // local queues to hold incoming packets pending comparison
  // store meaningful data, in non-working state, should not match to these data
  bit [keymgr_pkg::AdvDataWidth-1:0] adv_data_a_array[
    keymgr_dpe_pkg::DpeNumSlots][
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e];
  bit [keymgr_pkg::IdDataWidth-1:0]  id_data_a_array[
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e];
  bit [keymgr_pkg::GenDataWidth-1:0] sw_data_a_array[
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e];
  bit [keymgr_pkg::GenDataWidth-1:0] hw_data_a_array[
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e];
  keymgr_dpe_pkg::keymgr_dpe_policy_t key_policy;
  logic [keymgr_dpe_pkg::KeyVersionWidth-1:0] max_key_version;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    req_fifo = new("req_fifo", this);
    rsp_fifo = new("rsp_fifo", this);
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
        wait(cfg.keymgr_dpe_vif.keymgr_dpe_en_sync2 != lc_ctrl_pkg::On);

        if (cfg.en_cov) begin
          cov.lc_disable_cg.sample(current_state, get_operation,
                                   current_op_status == keymgr_pkg::OpWip);
        end

        if (current_state != keymgr_dpe_pkg::StWorkDpeReset ||
            current_op_status == keymgr_pkg::OpWip
        ) begin
          if (cfg.en_scb) wipe_hw_keys();
        end

        wait(cfg.keymgr_dpe_vif.keymgr_dpe_en_sync2 == lc_ctrl_pkg::On);
      end
    join_none
  endtask

  virtual function void process_kmac_data_req(kmac_app_item item);
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    bit is_err;
    logic [keymgr_dpe_pkg::DpeNumBootStagesWidth-1:0] boot_stage =
      current_internal_key[current_key_slot.src_slot].boot_stage;

    `uvm_info(`gfn, $sformatf("process_kmac_data_req: for op %s in state %s",
     op.name, current_state.name), UVM_MEDIUM)

    if (!cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
      compare_invalid_data(item.byte_data_q);
      return;
    end else begin
      // there must be a OP which causes the KMAC data req
      `DV_CHECK_EQ(current_op_status, keymgr_pkg::OpWip)
    end

    case (op)
      keymgr_dpe_pkg::OpDpeAdvance: begin
        // Invalid outputs and invalid operations should results in random data
        // for message data. 
        is_err = get_hw_invalid_input() || get_invalid_op();
        `uvm_info(`gfn, $sformatf("What is is_err: %d", is_err), UVM_MEDIUM)
        case (current_state)
          keymgr_dpe_pkg::StWorkDpeAvailable: begin
            if(boot_stage == 0) begin
              `uvm_info(`gfn, $sformatf("process_kmac_data_req: boot_stage %0d is_err %0d compare_boot_stage_0_data",
               boot_stage, is_err), UVM_LOW)
              compare_boot_stage_0_data(
                .exp_match(!is_err),
                .byte_data_q(item.byte_data_q)
              );
            end else if (boot_stage == 1) begin
              `uvm_info(`gfn, $sformatf("process_kmac_data_req: boot_stage %0d is_err %0d compare_boot_stage_1_data",
               boot_stage, is_err), UVM_LOW)
               compare_boot_stage_1_data(
                .exp_match(!is_err),
                .byte_data_q(item.byte_data_q)
               );
            end else begin
              `uvm_info(`gfn, $sformatf("process_kmac_data_req: boot_stage %0d is_err %0d compare_boot_stage_gte2_data",
               boot_stage, is_err), UVM_LOW)
               compare_boot_stage_gte2_data(
                .exp_match(!is_err),
                .byte_data_q(item.byte_data_q)
               );
            end
          end
          keymgr_dpe_pkg::StWorkDpeReset,
          keymgr_dpe_pkg::StWorkDpeDisabled,
          keymgr_dpe_pkg::StWorkDpeInvalid: begin
            // we'd expect that no kmac_data_req's would be issued in these states
            // set to 1 to check invalid data is used
            is_err = 1;
          end
          default: `uvm_error(`gfn, $sformatf("Unexpected current_state: %0d", current_state))
        endcase
        if (is_err) compare_invalid_data(item.byte_data_q);
      end
      keymgr_dpe_pkg::OpDpeGenSwOut, keymgr_dpe_pkg::OpDpeGenHwOut: begin
        case (current_state)
        keymgr_dpe_pkg::StWorkDpeAvailable: begin
          if (get_is_kmac_data_correct()) compare_gen_out_data(item.byte_data_q);
          else                            compare_invalid_data(item.byte_data_q);
        end
        keymgr_dpe_pkg::StWorkDpeReset,
        keymgr_dpe_pkg::StWorkDpeDisabled,
        keymgr_dpe_pkg::StWorkDpeInvalid: begin
          // we'd expect that no kmac_data_req's would be issued in these states
          // set to 1 to check invalid data is used
          is_err = 1;
        end
        default: `uvm_error(`gfn, $sformatf("Unexpected current_state: %0d", current_state))
        endcase
        if (is_err) compare_invalid_data(item.byte_data_q);
      end
      keymgr_dpe_pkg::OpDpeDisable: begin
        compare_invalid_data(item.byte_data_q);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
    endcase
  endfunction

  virtual function void process_kmac_data_rsp(kmac_app_item item);
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    update_result_e update_result;
    bit process_update;

    // fault error is preserved until reset
    if (!is_kmac_rsp_err) is_kmac_rsp_err = item.rsp_error;
    if (!is_kmac_invalid_data) is_kmac_invalid_data = item.get_is_kmac_rsp_data_invalid();

    update_result = process_update_after_op_done();

    `uvm_info(`gfn, $sformatf("process_kmac_data_rsp update_result %s for op %s in state %s with",
         update_result.name, op.name, current_state.name), UVM_MEDIUM)

    case (update_result)
      // Should occur when a valid OpDpeAdvance is issued in the StWorkDpeAvailable state
      UpdateInternalKey: begin
        // flag a key slot comparison
        compare_internal_key_slot = 1;
        // digest is 384 bits wide while internal key is only 256, need to truncate it
        current_internal_key[current_key_slot.dst_slot].key =
          {item.rsp_digest_share1[keymgr_pkg::KeyWidth-1:0],
           item.rsp_digest_share0[keymgr_pkg::KeyWidth-1:0]};

        // boot stage should increment between advance calls
        current_internal_key[current_key_slot.dst_slot].boot_stage =
          current_internal_key[current_key_slot.src_slot].boot_stage + 1;
        // valid is expected to be 1
        current_internal_key[current_key_slot.dst_slot].valid = 1;
        // key policy values should be set from the key_policy signal that was populated from the 
        // last slot_policy csr write before the "start" operation was enabled
        current_internal_key[current_key_slot.dst_slot].key_policy.allow_child = key_policy.allow_child;
        current_internal_key[current_key_slot.dst_slot].key_policy.exportable = key_policy.exportable;
        current_internal_key[current_key_slot.dst_slot].key_policy.retain_parent = key_policy.retain_parent;
        // max verssion should also be set from the max_version signal that was populated from the
        // last max_key_ver_shadowed csr write before the "start" operation was enabled
        current_internal_key[current_key_slot.dst_slot].max_key_version = max_key_version;

        cfg.keymgr_dpe_vif.store_internal_key(
          current_internal_key[current_key_slot.dst_slot].key, 
          current_state
        );

        `uvm_info(`gfn, $sformatf("Update internal key 0x%0h for op %s in state %s",
             current_internal_key[current_key_slot.dst_slot].key, op.name, current_state.name), UVM_MEDIUM)
      end
      // Should occur when a valid OpDpeGenSwOut is issued in the StWorkDpeAvailable state
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
      // Should occur when a valid OpDpeGenHwOut is issued in the StWorkDpeAvailable state
      UpdateHwOut: begin
        kmac_digests_t key_shares = {item.rsp_digest_share1, item.rsp_digest_share0};
        keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
            `gmv(ral.control_shadowed.dest_sel));

        if (dest != keymgr_pkg::None && !get_fault_err()) begin
          cfg.keymgr_dpe_vif.update_sideload_key(key_shares, current_state, dest);
          `uvm_info(`gfn, $sformatf("Update sideload key 0x%0h for %s", key_shares, dest.name),
                    UVM_MEDIUM)
        end
      end
      default: `uvm_info(`gfn, "KMAC result isn't updated to any output", UVM_MEDIUM)
    endcase
    // Don't update_kdf_key here, because the kmac_key_o signal is only visible when a start_en write
    // happens for one of the valid operations, and a kmac data req is issued.
    // if update_kdf_key occurs here, a comparison to zero will occur and create a false error.
  endfunction

  // update current_state, current_op_status, err_code, alert and return update_result for updating
  // internal key, HW/SW output when processing_kmac_data_rsp().
  virtual function update_result_e process_update_after_op_done();
    update_result_e update_result;
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();

    `uvm_info(`gfn,
      $sformatf("process_update_after_op_done: op %0s state %s",
        op.name, current_state.name), UVM_LOW)

    // Update state to Invalid earlier so that we can get InvalidOp error, as LC disable in the
    // middle of OP will trigger this error
    if (!cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) current_state = keymgr_dpe_pkg::StWorkDpeInvalid;

    // op_status is updated one cycle after done. If SW reads at this edge then it is still okay
    // to update this current_op_status as the status comparison can take OpWip as a legal value
    if (get_err_code() || get_fault_err()) begin 
      current_op_status = keymgr_pkg::OpDoneFail;
      `uvm_info(`gfn,
        $sformatf("process_update_after_op_done: op %0s state %s get_err_code %0d get_fault_err %0d",
          op.name, current_state.name, get_err_code(), get_fault_err()), UVM_LOW)
    end
    else begin
      current_op_status = keymgr_pkg::OpDoneSuccess;
    end

    if (cfg.en_cov && cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
      keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
          `gmv(ral.control_shadowed.dest_sel));
      cov.state_and_op_cg.sample(current_state, op, current_op_status, current_cdi, dest);
    end

    process_error_n_alert();
    void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
    if (cfg.en_cov && cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
      compare_op_e key_version_cmp;

      if (`gmv(ral.key_version[0]) > get_current_max_version) begin
        key_version_cmp = CompareOpGt;
      end else if (`gmv(ral.key_version[0]) == get_current_max_version) begin
        key_version_cmp = CompareOpEq;
      end else begin
        key_version_cmp = CompareOpLt;
        cov.key_version_compare_cg.sample(key_version_cmp, current_state, op);
      end 
    end

    // If we hit a fault error move to invalid state. 
    // If keymgr_dpe_en is not true then move to invalid state
    if (get_fault_err() || !cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
      update_state(keymgr_dpe_pkg::StWorkDpeInvalid);
      return NotUpdate;
    end

    case (current_state)
      keymgr_dpe_pkg::StWorkDpeAvailable: begin
        case (op)
          keymgr_dpe_pkg::OpDpeAdvance: begin
            // If there is an OP error then the internal key should not be updated
            if (get_op_err()) begin
              update_result = NotUpdate;
            end else begin
              update_result = UpdateInternalKey;
            end
          end
          keymgr_dpe_pkg::OpDpeGenSwOut,
          keymgr_dpe_pkg::OpDpeGenHwOut: begin
            // If there is a fault error then SW/HW key should not be updated
            // an op error will still cause a kmac engine operation. So still need to update
            // in order to avoid a false error in the scb/if
            if (get_fault_err()) begin
              update_result = NotUpdate;
            end else if (op == keymgr_dpe_pkg::OpDpeGenHwOut) begin
              update_result = UpdateHwOut;
            end else begin
              update_result = UpdateSwOut;
            end
          end
          default: begin
            // There should be nothing to update for StWorkDpeErase, StWorkDpeDisable
            update_result = NotUpdate;
          end
        endcase
      end
      keymgr_dpe_pkg::StWorkDpeDisabled,
      keymgr_dpe_pkg::StWorkDpeInvalid: begin
        case (op)
          keymgr_dpe_pkg::OpDpeAdvance, keymgr_dpe_pkg::OpDpeDisable: begin
            // Nothing should be updated for OpDpeAdvance in these states 
            update_result = NotUpdate;
          end
          keymgr_dpe_pkg::OpDpeGenSwOut: begin
            // A OpDpeGenSwOut Op can potentially cause an update to the SW share
            update_result = UpdateSwOut;
          end
          keymgr_dpe_pkg::OpDpeGenHwOut: begin
            // A OpDpeGenHwOut Op can potentially cause an update to the HW sideload
            update_result = UpdateHwOut;
          end
          default: `uvm_fatal(`gfn, $sformatf("Unexpected operation: %0s", op.name))
        endcase
      end
      // StWorkDpeReset would be an unexpected state becuase no KMAC data request should occur.
      default: `uvm_fatal(`gfn, $sformatf("Unexpected current_state: %0s", current_state.name))
    endcase // current_state
    return update_result;
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    dv_base_reg dv_reg;
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();


    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(dv_reg, csr)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      // sample regwen and its locked CSRs
      if (cfg.en_cov && cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
        bit cfg_regwen = (current_op_status == keymgr_pkg::OpWip);
        if (ral.cfg_regwen.locks_reg_or_fld(dv_reg)) begin
          if (csr.get_name() == "sideload_clear") begin
            cov.sideload_clear_cg.sample(`gmv(ral.sideload_clear.val),
                                        current_state,
                                        get_operation(),
                                        cfg.keymgr_dpe_vif.aes_sideload_status == SideLoadAvail,
                                        cfg.keymgr_dpe_vif.kmac_sideload_status == SideLoadAvail,
                                        cfg.keymgr_dpe_vif.otbn_sideload_status == SideLoadAvail,
                                        cfg_regwen);
          end else if (csr.get_name() != "control_shadowed") begin
            cov.sw_input_cg_wrap[csr.get_name()].sample(item.a_data, cfg_regwen);
          end
        end
      end
      if (cfg.en_cov && ral.sw_binding_regwen.locks_reg_or_fld(dv_reg)) begin
        cov.sw_input_cg_wrap[csr.get_name()].sample(
            item.a_data,
            `gmv(ral.sw_binding_regwen));
      end

      // if OP WIP or keymgr_dpe_en=0, will clear cfg_regwen and below csr can't be written
      if ((current_op_status == keymgr_pkg::OpWip || !cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) &&
          ral.cfg_regwen.locks_reg_or_fld(dv_reg)) begin
        `uvm_info(`gfn, $sformatf("Reg write to %s is ignored due to cfg_regwen=0", csr.get_name()),
                  UVM_MEDIUM)
        return;
      end else if ((`gmv(ral.sw_binding_regwen) == 0 || !cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) &&
          ral.sw_binding_regwen.locks_reg_or_fld(dv_reg)) begin
        `uvm_info(`gfn, $sformatf("Reg write to %0s is ignored due to sw_binding_regwen=0",
                                  csr.get_name()), UVM_MEDIUM)
        return;
      end else begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    if (data_phase_write && csr.get_name() == "sw_binding_regwen" &&
        current_state == keymgr_dpe_pkg::StWorkDpeReset) begin
      // in StWorkDpeReset, can't change sw_binding_regwen value
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
          bit [NumKeyMgrDpeIntr-1:0] intr_exp = `gmv(ral.intr_state);
          // intr_state always occurs after the OpDpeAdvance operation has completed
          // and the key slot has been updated. So we can use this state to check that
          // if the operation was OpDoneSuccess, and the intr was triggered then the
          // target key slot can be checked against our expected key slot values
          `uvm_info(`gfn, $sformatf("intr_state: status is %s compare_internal_key_slot %0d",
            current_op_status.name, compare_internal_key_slot), UVM_MEDIUM)
          if (current_op_status == keymgr_pkg::OpDoneSuccess && compare_internal_key_slot) begin
              cfg.keymgr_dpe_vif.compare_internal_key_slot(
                current_internal_key[current_key_slot.dst_slot],
                current_internal_key[current_key_slot.src_slot],
                current_key_slot.dst_slot,
                current_key_slot.src_slot,
                current_internal_key[current_key_slot.src_slot].key_policy.retain_parent
              );
            compare_internal_key_slot = 0;
          end

          foreach (intr_exp[i]) begin
            keymgr_dpe_intr_e intr = keymgr_dpe_intr_e'(i);

            `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[i], (intr_en[i] & intr_exp[i]),
                           $sformatf("Interrupt_pin: %0s", intr.name));

            if (cfg.en_cov) begin
              cov.intr_cg.sample(intr, intr_en[intr], intr_exp[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
            end
          end
        end
      end
      "intr_enable", "sw_binding_regwen": begin
        // no speical handle is needed
      end
      "err_code": begin
        // Check in this block
        do_read_check = 1'b0;

        if (data_phase_read) begin
          bit [TL_DW-1:0] err_code = `gmv(ral.err_code);

          `DV_CHECK_EQ(item.d_data[keymgr_pkg::ErrInvalidOp],
                       err_code[keymgr_pkg::ErrInvalidOp])

          // skip checking ErrShadowUpdate as it's done in common direct sequence where we disable
          // the scb

          // when op error occurs with keymgr_dpe_en = 0,
          // input is meaningless. Design may or may not
          // assert ErrInvalidIn, which doesn't matter
          if (!err_code[keymgr_pkg::ErrInvalidOp] && cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
            `DV_CHECK_EQ(item.d_data[keymgr_pkg::ErrInvalidIn],
                         err_code[keymgr_pkg::ErrInvalidIn])
          end

          if (cfg.en_cov) begin
            if (err_code[keymgr_pkg::ErrInvalidOp]) begin
              cov.err_code_cg.sample(keymgr_pkg::ErrInvalidOp);
            end
            if (err_code[keymgr_pkg::ErrInvalidIn]) begin
              cov.err_code_cg.sample(keymgr_pkg::ErrInvalidIn);
            end
          end
        end
      end
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
          bit [NumKeyMgrDpeIntr-1:0] intr_exp = `gmv(ral.intr_state) | item.a_data;

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

        // skip checking cfg_regwen value when it's advance OP in Reset,
        // as it's hard to know what exact
        // time OP will complete
        if (current_state != keymgr_dpe_pkg::StWorkDpeReset ||
            current_op_status != keymgr_pkg::OpWip) begin
          if (addr_phase_read) begin
            addr_phase_cfg_regwen = current_op_status != keymgr_pkg::OpWip &&
                               cfg.keymgr_dpe_vif.get_keymgr_dpe_en();
          end else if (data_phase_read) begin
            `DV_CHECK_EQ(item.d_data, addr_phase_cfg_regwen)
          end
        end
      end
      "slot_policy": begin
        // Capture the latest key policy write
        // only valid when start is enabled
        if (addr_phase_write) begin
          key_policy.allow_child   = item.a_data[0];
          key_policy.exportable    = item.a_data[1];
          key_policy.retain_parent = item.a_data[2];
          `uvm_info(`gfn,
            $sformatf("key_policy write with item.a_data 'h%h, key_policy = %p",
              item.a_data, key_policy), UVM_LOW)
        end
      end
      "start": begin
        if (addr_phase_write) begin
          bit start = `gmv(ral.start.en);
          // compare key is used to either store an invalid key or the
          // current valid internal key for an advance operation.
          keymgr_dpe_pkg::keymgr_dpe_slot_t compare_key;
          bit good_key;
          bit good_data;

          if (start) begin
            get_key_slots();
            current_op_status = keymgr_pkg::OpWip;

            `uvm_info(`gfn, $sformatf("Start: At %s, %s is issued",
               current_state.name, op.name), UVM_LOW)

            case (current_state)
              keymgr_dpe_pkg::StWorkDpeReset: begin
                case (op)
                  keymgr_dpe_pkg::OpDpeAdvance: begin
                    // Expect no EDN request is issued. After this advance is done, will have 2 reqs
                    `DV_CHECK_EQ(edn_fifos[0].is_empty(), 1)
                     latch_otp_key();

                     // Call this after latch_otp_key, as get_is_kmac_key_correct/get_hw_invalid_input
                     // needs to know what if the key is valid
                     good_key = get_is_kmac_key_correct();
                     good_data = good_key && get_sw_invalid_input() && get_hw_invalid_input();

                     if (!good_key) begin
                       // If invalid key is used, design will switch to use random data for the
                       // operation. Set a non all 0s/1s data (use 1 here) for them in scb, so that it
                       // doesn't lead to an invalid_key error
                       current_internal_key[current_key_slot.dst_slot].key[0] = 1;
                       current_internal_key[current_key_slot.dst_slot].key[1] = 1;
                     end
                  end
                  default: begin // !OpDpeAdvance
                    // any operation aside from advance will lead to a failed operation
                    current_op_status = keymgr_pkg::OpDoneFail;
                    // No KDF issued, done interrupt/alert is triggered in next cycle
                    void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
                    if (cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) fork
                      begin
                        cfg.clk_rst_vif.wait_clks(1);
                        process_error_n_alert();

                        if (cfg.en_cov) begin
                          keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
                              `gmv(ral.control_shadowed.dest_sel));

                          cov.state_and_op_cg.sample(current_state, op, current_op_status,
                              current_cdi, dest);
                        end
                      end
                    join_none
                    void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));
                  end
                endcase
              end
              keymgr_dpe_pkg::StWorkDpeAvailable: begin
                case (op)
                  keymgr_dpe_pkg::OpDpeAdvance, keymgr_dpe_pkg::OpDpeGenSwOut, keymgr_dpe_pkg::OpDpeGenHwOut: begin
                    good_key = get_is_kmac_key_correct();
                    good_data = good_key && get_sw_invalid_input() && get_hw_invalid_input();
                    if (!good_key) begin
                      // if invalid key is used, design will switch to use random data for the
                      // operation. Set a non all 0s/1s data (use 1 here) for them in scb, so that it
                      // doesn't lead to an invalid_key error
                      compare_key.key[0] = 1;
                      compare_key.key[1] = 1;
                    end begin
                      compare_key.key = current_internal_key[current_key_slot.src_slot].key;
                    end
                    // update kmac key for check
                    if (current_internal_key[current_key_slot.src_slot].key > 0) begin
                      `uvm_info(`gfn,
                      $sformatf("start: update_kdf_key:\n key[0] 'h%h\nkey[1] 'h%h\n good key %0d, good_data %0d",
                      current_internal_key[current_key_slot.src_slot].key[0], current_internal_key[current_key_slot.src_slot].key[1], good_key, good_data), UVM_LOW)
                      cfg.keymgr_dpe_vif.update_kdf_key(
                        compare_key.key,
                        current_state,
                        good_key,
                        good_data
                      );
                    end
                  end
                  keymgr_dpe_pkg::OpDpeErase: begin
                    // TODO(#667) add handling of erase  and disable in "start" case of
                    // process_tl_access
                  end
                  keymgr_dpe_pkg::OpDpeDisable: begin
                  end
                endcase
              end
              keymgr_dpe_pkg::StWorkDpeDisabled: begin
                // TODO(#667) add handling of disabled and invalid states in "start" case of
                // process_tl_access
              end
              keymgr_dpe_pkg::StWorkDpeInvalid: begin
                // TODO(#667) add handling of disabled and invalid states in "start" case of
                // process_tl_access
              end
              default: begin
                `uvm_fatal(`gfn, $sformatf("process_tl_access: unrecognized state in the start case"))
              end
            endcase
          end // start
        end else if (addr_phase_read) begin
          // start drops when op is done.
          void'(csr.predict(.value(current_op_status == keymgr_pkg::OpWip),
                            .kind(UVM_PREDICT_READ)));
        end
      end
      "working_state": begin
        // Check in this block
        do_read_check = 1'b0;

        if (addr_phase_read) begin
          addr_phase_working_state = current_state;
        end else if (data_phase_read) begin
          // scb can't predict when advance from StWorkDpeReset is done,
          // as it's updated internally and no
          // output to indicate that, skip checking it
          if (current_state != keymgr_dpe_pkg::StWorkDpeReset ||
              current_op_status != keymgr_pkg::OpWip) begin
            keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e act_state;

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
          if (current_state inside {keymgr_dpe_pkg::StWorkDpeReset,
                                    keymgr_dpe_pkg::StWorkDpeAvailable}) begin
            // when advance from StWorkDpeReset to StWorkDpeAvailable
            // we don't know how long it will take, it's ok
            // when status is WIP or success
            // TODO(#667) - need to restructure SCB so that reading a WIP status doesn't cause an error
            // when current_op_status is equal to OpDoneSuccess
            if (cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
              `DV_CHECK_EQ(item.d_data inside {
                 current_op_status, keymgr_pkg::OpDoneSuccess,
                 keymgr_pkg::OpWip},
                 1
              )
            end
            // advance OP completes
            if (current_op_status == keymgr_pkg::OpWip && 
                item.d_data inside {keymgr_pkg::OpDoneSuccess, keymgr_pkg::OpDoneFail}) begin
              current_op_status = keymgr_pkg::keymgr_op_status_e'(item.d_data);

              if (cfg.en_cov) begin
                keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
                    `gmv(ral.control_shadowed.dest_sel));

                cov.state_and_op_cg.sample(current_state, get_operation(), current_op_status,
                    current_cdi, dest);
              end

              current_state = get_next_state(current_state);
              void'(ral.intr_state.predict(.value(1 << int'(IntrOpDone))));

              // keymgr_dpe should request 2 EDN data during advancing from StWorkDpeReset
              // function `used` returns the number of entries put into the FIFO
              `DV_CHECK_EQ(edn_fifos[0].used(), 2)
            end
          end else begin
            `DV_CHECK_EQ(item.d_data, addr_phase_op_status)
          end
        end
      end
      "reseed_interval_shadowed": begin
        if (addr_phase_write) begin
          cfg.keymgr_dpe_vif.edn_interval = `gmv(ral.reseed_interval_shadowed.val);

          if (cfg.en_cov) cov.reseed_interval_cg.sample(`gmv(ral.reseed_interval_shadowed.val));
        end
      end
      "sideload_clear": begin
        if (addr_phase_write) begin
          fork
            begin
              cfg.clk_rst_vif.wait_clks(1);
              cfg.keymgr_dpe_vif.clear_sideload_key(
                  keymgr_pkg::keymgr_sideload_clr_e'(`gmv(ral.sideload_clear.val)));
            end
          join_none
        end
      end
      "max_key_ver_shadowed": begin
        if(addr_phase_write) begin
          if (cfg.en_cov) 
            cov.sw_input_cg_wrap["max_key_ver_shadowed"].sample(item.a_data,
                `gmv(ral.max_key_ver_regwen));
          max_key_version = item.a_data[31:0];
          `uvm_info(`gfn, 
            $sformatf("max_key_ver_shadowed was written with max_key_version value %0d",
              max_key_version), UVM_LOW)

        end
      end
      "fault_status": begin
        // Check in this block
        do_read_check = 1'b0;

        if (data_phase_read) begin
          `DV_CHECK_EQ(item.d_data[keymgr_pkg::FaultKmacOp],  is_kmac_rsp_err)
          `DV_CHECK_EQ(item.d_data[keymgr_pkg::FaultKmacOut], is_kmac_invalid_data)
        end
      end
      "debug": begin
        // do nothing
      end
      default: begin
        if (!uvm_re_match("sw_share*", csr.get_name())) begin // sw_share
          // if keymgr_dpe isn't On, SW output should be entropy and not match to predict value
          if (addr_phase_read) begin
            addr_phase_is_sw_share_corrupted = is_sw_share_corrupted;
          end else if (data_phase_read && addr_phase_is_sw_share_corrupted) begin
            // disable read check outside of the item compare.
            // it is possible for the returned data when corrupted, to be 0
            do_read_check = 1'b0;
            if (item.d_data != 0) begin
              `DV_CHECK_NE(item.d_data, `gmv(csr))
            end
          end
        end else begin // Not sw_share
          // ICEBOX(#18344): explicitly list all the unchecked regs here.
          do_read_check = 1'b0;
          $display("process_tl_access: a csr %0s was received that isn't handled", csr.get_name());
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

  virtual function void latch_otp_key();
    key_shares_t otp_key;
    if (cfg.keymgr_dpe_vif.otp_key.creator_root_key_share0_valid &&
        cfg.keymgr_dpe_vif.otp_key.creator_root_key_share1_valid) begin
      otp_key = {cfg.keymgr_dpe_vif.otp_key.creator_root_key_share1,
                 cfg.keymgr_dpe_vif.otp_key.creator_root_key_share0};
    end else begin
      if (cfg.en_cov) cov.invalid_hw_input_cg.sample(OtpRootKeyValidLow);
      `uvm_info(`gfn, "otp_key valid is low", UVM_LOW)
    end
    current_internal_key[current_key_slot.dst_slot].valid = 1;
    current_internal_key[current_key_slot.dst_slot].boot_stage = 0;
    current_internal_key[current_key_slot.dst_slot].max_key_version = max_key_version;
    current_internal_key[current_key_slot.dst_slot].key = otp_key;
    current_internal_key[current_key_slot.dst_slot].key_policy = '0;
    current_internal_key[current_key_slot.dst_slot].key_policy.allow_child = 1;
    `uvm_info(`gfn,
      $sformatf("latch_otp_key: key %p",
      current_internal_key[current_key_slot.dst_slot]
      ),
      UVM_MEDIUM)
    cfg.keymgr_dpe_vif.store_internal_key(
      current_internal_key[current_key_slot.dst_slot].key,
      current_state
    );
  endfunction

  virtual function bit [TL_DW-1:0] get_current_max_version(
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e state = current_state);
    // design change this to 0 if LC turns off keymgr_dpe.
    if (!cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) return 0;
    return `gmv(ral.max_key_ver_shadowed);
  endfunction

  virtual function void process_error_n_alert();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    bit [TL_DW-1:0] err = get_err_code();

    void'(ral.err_code.predict(err));

    if (get_fault_err() || !cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) begin
      is_sw_share_corrupted = 1;
      cfg.keymgr_dpe_vif.wipe_sideload_keys();
      `uvm_info(`gfn, $sformatf("proces_error_n_alert: at %s, %s is issued and error %s",
                current_state.name, op.name, "sw_share_corrupted"), UVM_MEDIUM)
    end

    if (get_fault_err()) begin
      set_exp_alert("fatal_fault_err", .is_fatal(1));
      `uvm_info(`gfn, $sformatf("process_error_n_alert: at %s, %s is issued and error %s",
                current_state.name, op.name, "get_fault_err"), UVM_MEDIUM)
    end

    if (get_op_err()) begin 
      set_exp_alert("recov_operation_err");
      `uvm_info(`gfn, $sformatf("process_error_n_alert: at %s, %s is issued and error %s",
                current_state.name, op.name, "recov_operation_err"), UVM_MEDIUM)
    end

  endfunction

  virtual function bit [TL_DW-1:0] get_fault_err();
    return is_kmac_rsp_err | is_kmac_invalid_data;
  endfunction

  virtual function bit [TL_DW-1:0] get_op_err();
    bit [TL_DW-1:0] err = get_err_code();
    bit fault = get_fault_err();

    // A detected fault causes the operation to transition into invalid,
    // which will report an invalid operation
    return err[keymgr_pkg::ErrInvalidOp] || err[keymgr_pkg::ErrInvalidIn] ||
      fault;
  endfunction

  virtual function bit [TL_DW-1:0] get_err_code();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    bit [TL_DW-1:0] err_code;

    // A detected fault will cause us to transition to invalid where
    // operations are always error'd
    err_code[keymgr_pkg::ErrInvalidOp] = get_invalid_op() | get_fault_err();

    err_code[keymgr_pkg::ErrInvalidIn] = get_hw_invalid_input() | get_sw_invalid_input();

    `uvm_info(`gfn, $sformatf({"op_err = %0d, rsp_err = %0d, hw_invalid = %0d, sw_invalid = %0d, ",
              "kmac_invalid_data = %0d"},
              get_invalid_op(), is_kmac_rsp_err, get_hw_invalid_input(), get_sw_invalid_input(),
              is_kmac_invalid_data), UVM_MEDIUM)
    return err_code;
  endfunction

  virtual function bit get_invalid_op();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    `uvm_info(`gfn, $sformatf("get_invalid_op: op %s current_state: %s",
       op.name, current_state.name), UVM_MEDIUM)
    case (current_state)
      keymgr_dpe_pkg::StWorkDpeReset : begin
        if (get_operation() != keymgr_dpe_pkg::OpDpeAdvance) begin
          return 1;
        end
      end
      keymgr_dpe_pkg::StWorkDpeAvailable: begin
        case (op)
          keymgr_dpe_pkg::OpDpeAdvance: begin
            // invalid op if src boot_stage is equal to current boot stage
            if (current_internal_key[current_key_slot.src_slot].boot_stage >=
                (keymgr_dpe_pkg::DpeNumBootStages-1)
            ) begin
              `uvm_info(`gfn, $sformatf("get_invalid_op: op %s current_state: %s boot_stage err",
                op.name, current_state.name), UVM_MEDIUM)
              return 1;
            end
            // invalid op if dst slot == src slot and retain_parent == 1
            if ((current_internal_key[current_key_slot.src_slot].key_policy.retain_parent == 1) &&
                current_key_slot.src_slot == current_key_slot.dst_slot
            ) begin
              `uvm_info(`gfn, $sformatf("get_invalid_op: op %s current_state: %s retain_parent == 1 err",
                op.name, current_state.name), UVM_MEDIUM)
              return 1;
            end
            // invalid op if dst slot != src slot and retain_parent == 0
            if ((current_internal_key[current_key_slot.src_slot].key_policy.retain_parent == 0) &&
                current_key_slot.src_slot != current_key_slot.dst_slot
            ) begin
              `uvm_info(`gfn, $sformatf("get_invalid_op: op %s current_state: %s retain_parent == 0 err",
                op.name, current_state.name), UVM_MEDIUM)
              return 1;
            end
            // invalid op src_slot is invalid. Src slot could have been "erased"
            if (current_internal_key[current_key_slot.src_slot].valid == 0) begin
              `uvm_info(`gfn, $sformatf("get_invalid_op: op %s current_state: %s valid == 0 err",
                op.name, current_state.name), UVM_MEDIUM)
              return 1;
            end
            return 0;
          end
          keymgr_dpe_pkg::OpDpeGenSwOut, keymgr_dpe_pkg::OpDpeGenHwOut: begin
            if (!current_internal_key[current_key_slot.src_slot].valid)
              return 1;
            return 0;
          end
          default: begin
          end
        endcase
      end
      keymgr_dpe_pkg::StWorkDpeDisabled, keymgr_dpe_pkg::StWorkDpeInvalid: begin
        return 1;
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected state %s", current_state.name))
    endcase
    return 0;
  endfunction

  virtual function bit get_sw_invalid_input();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    if (op inside {keymgr_dpe_pkg::OpDpeGenSwOut, keymgr_dpe_pkg::OpDpeGenHwOut}) begin
      if (current_state == keymgr_dpe_pkg::StWorkDpeAvailable &&
          current_internal_key[current_key_slot.src_slot].valid &&
          get_current_max_version() >= `gmv(ral.key_version[0])
      ) begin
        return 0;
      end else begin
        void'(ral.debug.invalid_key_version.predict(1));
        return 1;
      end
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
    int err_cnt;
    keymgr_dpe_invalid_hw_input_type_e invalid_hw_input_type;

    // if it's an invalid op, kmac key and data are random value, they shouldn't be all 0s/1s
    if (get_invalid_op() || get_operation() == keymgr_dpe_pkg::OpDpeDisable) return 0;

    if ((current_internal_key[current_key_slot.src_slot].key[0] inside {0, '1} ||
         current_internal_key[current_key_slot.src_slot].key[1] inside {0, '1}) &&
         current_state != keymgr_dpe_pkg::StWorkDpeReset) begin
      invalid_hw_input_type = OtpRootKeyInvalid;
      void'(ral.debug.invalid_key.predict(1));
      err_cnt++;
      `uvm_info(`gfn, $sformatf("internal key for %s %s is invalid", current_state, current_cdi),
                UVM_LOW)
    end

    if (get_operation() != keymgr_dpe_pkg::OpDpeAdvance) return err_cnt > 0;

      if (cfg.keymgr_dpe_vif.keymgr_dpe_div inside {0, '1}) begin
        invalid_hw_input_type = LcStateInvalid;
        void'(ral.debug.invalid_health_state.predict(1));
        err_cnt++;
        `uvm_info(`gfn, "HW invalid input on keymgr_dpe_div", UVM_LOW)
      end

      if (cfg.keymgr_dpe_vif.otp_device_id inside {0, '1}) begin
        invalid_hw_input_type = OtpDevIdInvalid;
        void'(ral.debug.invalid_dev_id.predict(1));
        err_cnt++;
        `uvm_info(`gfn, "HW invalid input on otp_device_id", UVM_LOW)
      end

      for (int i = 0; i < keymgr_dpe_reg_pkg::NumRomDigestInputs; ++i) begin
        if (cfg.keymgr_dpe_vif.rom_digests[i].data inside {0, '1}) begin
          invalid_hw_input_type = RomDigestInvalid;
          void'(ral.debug.invalid_digest.predict(1));
          err_cnt++;
          `uvm_info(`gfn, $sformatf("HW invalid input on rom_digests[%0d]", i), UVM_LOW)
        end

        if (!cfg.keymgr_dpe_vif.rom_digests[i].valid) begin
          invalid_hw_input_type = RomDigestValidLow;
          void'(ral.debug.invalid_digest.predict(1));
          err_cnt++;
          `uvm_info(`gfn,
                    $sformatf("HW invalid input, rom_digests[%0d].valid is low", i),
                    UVM_LOW)
        end
      end

    // Sample error when there is only one error to make sure each error can cause operation to
    // fail
    if (err_cnt == 1 && cfg.en_cov) begin
      cov.invalid_hw_input_cg.sample(invalid_hw_input_type);
    end
    return err_cnt > 0;
  endfunction

  // in normal operational states, invalid command etc lead to random data for gen-out OP
  virtual function bit get_is_kmac_data_correct();
    bit [TL_DW-1:0] err_code = get_err_code();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();

    if (current_state == keymgr_dpe_pkg::StWorkDpeAvailable) begin
      return !(get_fault_err() |
               err_code[keymgr_pkg::ErrInvalidIn]  |
               !cfg.keymgr_dpe_vif.get_keymgr_dpe_en());
    end else begin
      return 0;
    end
  endfunction

  // Entering StDisable or invalid op leads to random key
  virtual function bit get_is_kmac_key_correct();
    bit [TL_DW-1:0] err_code = get_err_code();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    return !(err_code[keymgr_pkg::ErrInvalidOp]) && !get_fault_err();
  endfunction

  virtual function void compare_boot_stage_0_data(
      bit exp_match,
      const ref byte byte_data_q[$]
  );
    adv_creator_data_t exp, act;
    string str = $sformatf("src_slot: %0d\n", current_key_slot.src_slot);

    if (exp_match) `DV_CHECK_EQ(byte_data_q.size, keymgr_pkg::AdvDataWidth / 8)
    act = {<<8{byte_data_q}};

    exp.DiversificationKey = cfg.keymgr_dpe_vif.flash.seeds[flash_ctrl_pkg::CreatorSeedIdx];
    for (int i = 0; i < keymgr_dpe_reg_pkg::NumRomDigestInputs; ++i) begin
      exp.RomDigests[i] = cfg.keymgr_dpe_vif.rom_digests[i].data;
    end
    exp.HealthMeasurement  = cfg.keymgr_dpe_vif.keymgr_dpe_div;
    exp.DeviceIdentifier   = cfg.keymgr_dpe_vif.otp_device_id;
    exp.HardwareRevisionSecret = keymgr_pkg::RndCnstRevisionSeedDefault;

    get_sw_binding_mirrored_value(exp.SoftwareBinding);

    // The order of the string creation must match the design
    `CREATE_CMP_STR(DiversificationKey)
    `CREATE_CMP_STR(RomDigests)
    `CREATE_CMP_STR(HealthMeasurement)
    `CREATE_CMP_STR(DeviceIdentifier)
    `CREATE_CMP_STR(HardwareRevisionSecret)
    `CREATE_CMP_STR(SoftwareBinding)

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[current_key_slot.src_slot][current_state] = act;
  endfunction

  virtual function void compare_boot_stage_1_data(
      bit exp_match,
      const ref byte byte_data_q[$]
    );
    adv_owner_int_data_t exp, act;
    string str = $sformatf("src_slot: %0d\n", current_key_slot.src_slot);

    act = {<<8{byte_data_q}};

    exp.OwnerRootSecret = cfg.keymgr_dpe_vif.flash.seeds[flash_ctrl_pkg::OwnerSeedIdx];
    get_sw_binding_mirrored_value(exp.SoftwareBinding);

    `CREATE_CMP_STR(unused)
    `CREATE_CMP_STR(OwnerRootSecret)
    for (int i = 0; i < keymgr_dpe_reg_pkg::NumSwBindingReg; i++) begin
      `CREATE_CMP_STR(SoftwareBinding[i])
    end

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[current_key_slot.src_slot][current_state] = act;
  endfunction

  virtual function void compare_boot_stage_gte2_data(
     bit exp_match,
     const ref byte byte_data_q[$]
   );
    adv_owner_data_t exp, act;
    string str = $sformatf("src_slot: %0d\n", current_key_slot.src_slot);

    act = {<<8{byte_data_q}};

    get_sw_binding_mirrored_value(exp.SoftwareBinding);

    `CREATE_CMP_STR(unused)
    for (int i=0; i < keymgr_dpe_reg_pkg::NumSwBindingReg; i++) begin
      `CREATE_CMP_STR(SoftwareBinding[i])
    end

    if (exp_match) begin
      `DV_CHECK_EQ(act, exp, str)
    end else begin
      `DV_CHECK_NE(act, exp, str)
    end

    if (exp_match) adv_data_a_array[current_key_slot.src_slot][current_state] = act;
  endfunction

  // for invalid OP, should not output any meaningful data to KMAC. Check the outputs aren't
  // matching to any of existing meaningful data
  virtual function void compare_invalid_data(const ref byte byte_data_q[$]);
    adv_owner_data_t act;

    act = {<<8{byte_data_q}};
    foreach (adv_data_a_array[i, j]) begin
      `DV_CHECK_NE(act, adv_data_a_array[i][j], $sformatf("Adv data to state %0s for slot %0d", j.name,
                                                          i))
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
    foreach (cfg.keymgr_dpe_vif.keys_a_array[state, dest]) begin
      `DV_CHECK_NE(act, cfg.keymgr_dpe_vif.keys_a_array[state][dest],
                   $sformatf("key at state %0d for%s", state, dest))
    end
  endfunction

  virtual function void compare_gen_out_data(const ref byte byte_data_q[$]);
    gen_out_data_t exp, act;
    keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation();
    keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::keymgr_key_dest_e'(
            `gmv(ral.control_shadowed.dest_sel));
    string str;

    act = {<<8{byte_data_q}};

    exp.KeyVersion = `gmv(ral.key_version[0]);
    for (int i = 0; i < keymgr_dpe_reg_pkg::NumSaltReg; i++) begin
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
      keymgr_dpe_pkg::OpDpeGenSwOut: begin
        exp.SoftwareExportConstant = keymgr_pkg::RndCnstSoftOutputSeedDefault;
        sw_data_a_array[current_state] = act;
      end
      keymgr_dpe_pkg::OpDpeGenHwOut: begin
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

  virtual function keymgr_dpe_cdi_type_e get_adv_cdi_type();
    `downcast(get_adv_cdi_type, adv_cnt)
  endfunction

  virtual function void get_sw_binding_mirrored_value(
        output bit [keymgr_dpe_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] sw_binding
      );

    for (int i = 0; i < keymgr_dpe_reg_pkg::NumSwBindingReg; i++) begin
      sw_binding[i] = `gmv(ral.sw_binding[i]);
    end
  endfunction

  // if it's not defined operation, treat as OpDpeDisable
  virtual function keymgr_dpe_pkg::keymgr_dpe_ops_e get_operation();
    keymgr_dpe_pkg::keymgr_dpe_ops_e op;
    int op_int_val = `gmv(ral.control_shadowed.operation);

    if (!$cast(op, op_int_val)) op = keymgr_dpe_pkg::OpDpeDisable;
    return op;
  endfunction

  virtual function void get_key_slots();
    current_key_slot.src_slot = `gmv(ral.control_shadowed.slot_src_sel);
    current_key_slot.dst_slot = `gmv(ral.control_shadowed.slot_dst_sel);
    `uvm_info(`gfn, $sformatf("get_key_slots %p", current_key_slot), UVM_LOW)
  endfunction

  virtual function keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e get_next_state(
      keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e cur = current_state,
      keymgr_dpe_pkg::keymgr_dpe_ops_e op = get_operation()
    );
    if (!cfg.keymgr_dpe_vif.get_keymgr_dpe_en()) return keymgr_dpe_pkg::StWorkDpeInvalid;
    else return keymgr_dpe_env_pkg::get_next_state(cur, op);
  endfunction

  virtual function void update_state(
      keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e new_state = get_next_state(),
      int cyc_dly = 1);
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
    fork
      begin
        uvm_reg_data_t current_design_state;
        cfg.clk_rst_vif.wait_n_clks(1);
        // When LC disables keymgr_dpe across with an operation, will have InvalidOp error.
        // If no operation at that time, no error.
        // Need to know the actual state in design, in order to predict correctly
        // And we will check that hw key is wiped no matter whether InvalidOp is set or not.
        csr_rd(.ptr(ral.working_state), .value(current_design_state), .backdoor(1'b1));

        // TODO(opentitan-integrated/issues/667):
        // re-evaluate wipe_hw_keys() function for the state StInit
        // which is no longer valid for keymgr_dpe

        // LC-disable happens during advancing to StWorkDpeInit
        // If LC-disable happens during an operation in other states, KDF will occur.
        // err_code/alert is updated when KDF is done
        //if (current_design_state == keymgr_dpe_pkg::StWorkDpeInit) begin
        //  bit [TL_DW-1:0] err_code = get_err_code();
        //  err_code[keymgr_pkg::ErrInvalidOp] = 1;
        //  // if it's StWorkDpeInit, the Advance OP is ongoing. alert will be sent after the OP
        //  set_exp_alert("recov_operation_err", .max_delay(RESET_ADV_CYCLES));
        //  void'(ral.err_code.predict(err_code));
        //  `uvm_info(`gfn,
        //      "keymgr_dpe_en is Off when advancing to StWorkDpeInit,\
        //      wipe secret and move state to Invalid",
        //        UVM_LOW)
        //end
        //else if (current_op_status != keymgr_pkg::OpWip) begin
        //  update_state(.cyc_dly(2));
        //  `uvm_info(`gfn, "keymgr_dpe_en is Off, wipe secret and move state to Invalid", UVM_LOW)
        //end
      end
      begin
        // it takes 2 cycle to wipe sw_share. add one more negedge to avoid race condition
        // corner case
        cfg.clk_rst_vif.wait_n_clks(3);
        cfg.keymgr_dpe_vif.wipe_sideload_keys();
        is_sw_share_corrupted = 1;
      end
    join_none
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    current_state         = keymgr_dpe_pkg::StWorkDpeReset;
    current_op_status     = keymgr_pkg::OpIdle;
    is_kmac_rsp_err       = 0;
    is_kmac_invalid_data  = 0;
    is_sw_share_corrupted = 0;
    req_fifo.flush();
    rsp_fifo.flush();
    foreach (current_internal_key[slot]) begin
      current_internal_key[slot].key = '0;
      current_internal_key[slot].key_policy = '0;
      current_internal_key[slot].boot_stage = '0;
      current_internal_key[slot].max_key_version = '0;
      current_internal_key[slot].valid = '0;
    end
    foreach (adv_data_a_array[slot, state]) begin
      adv_data_a_array[slot][state] = '0;
    end
    id_data_a_array.delete();
    sw_data_a_array.delete();
    hw_data_a_array.delete();
    cfg.keymgr_dpe_vif.reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(kmac_app_item, req_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(kmac_app_item, rsp_fifo)
    if (compare_internal_key_slot)
      `uvm_error(`gfn,
        $sformatf("outstanding compare_internal_key_slot left unchecked %0d",
          compare_internal_key_slot))
  endfunction

  `undef CREATE_CMP_STR
endclass
