// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_dpe_if(input clk, input rst_n);

  import uvm_pkg::*;
  import keymgr_dpe_env_pkg::*;
  import keymgr_dpe_reg_pkg::NumRomDigestInputs;

  // Represents the keymgr_dpe sideload state for each sideload interface.
  //
  // The initial status is SideLoadNotAvail. After the sideload key is generated, it becomes
  // SideLoadAvail.
  // Status can't be directly changed from SideLoadClear to SideLoadAvail.
  // When status is SideLoadClear due to SIDELOAD_CLEAR programmed, need to write CSR to 0 to reset
  // it so that status is changed to SideLoadNotAvail, then we may set it to SideLoadAvail again
  lc_ctrl_pkg::lc_tx_t                                keymgr_dpe_en;
  lc_ctrl_pkg::lc_keymgr_div_t                        keymgr_dpe_div;
  otp_ctrl_pkg::otp_device_id_t                       otp_device_id;
  otp_ctrl_pkg::otp_keymgr_key_t                      otp_key;
  flash_ctrl_pkg::keymgr_flash_t                      flash;
  rom_ctrl_pkg::keymgr_data_t[NumRomDigestInputs-1:0] rom_digests;

  keymgr_pkg::hw_key_req_t kmac_key;
  keymgr_pkg::hw_key_req_t aes_key;
  keymgr_pkg::otbn_key_req_t otbn_key;

  keymgr_pkg::hw_key_req_t kmac_key_exp;
  keymgr_pkg::hw_key_req_t aes_key_exp;
  keymgr_pkg::otbn_key_req_t otbn_key_exp;

  // connect KDF interface for assertion check
  wire kmac_pkg::app_req_t kmac_data_req;
  wire kmac_pkg::app_rsp_t kmac_data_rsp;

  // connect EDN for assertion check
  wire edn_clk, edn_rst_n, edn_req, edn_ack;

  // connect to PRNG to track PRNG updates for EDN assertion
  wire lfsr_en;

  // keymgr_dpe_en is async, create a sync one for use in scb
  lc_ctrl_pkg::lc_tx_t keymgr_dpe_en_sync1, keymgr_dpe_en_sync2;

  // indicate if check the key is same as expected or shouldn't match to any meaningful key
  // when a good KDF is ongoing or kmac sideload key is available, this flag is set to 1
  bit is_kmac_key_good;

  // KMAC data is checked in scb, but when keymgr_dpe is in
  // disabled/invalid state or LC is off, KMAC
  // data will be driven with constantly changed entropy data, which violate
  // H_DataStableWhenValidAndNotReady_A. Use this flag to disable it
  bit is_kmac_data_good;

  // sideload status
  keymgr_dpe_sideload_status_e aes_sideload_status;
  keymgr_dpe_sideload_status_e otbn_sideload_status;

  // When kmac sideload key is generated, `kmac_key` becomes valid with the generated digest data.
  // If SW requests keymgr_dpe to do another operation, kmac_key will be updated to the internal key
  // to perform a KMAC KDF operation.
  // Once the operation is done, `kmac_key` is expected to switch automatically to the previous KMAC
  // sideload key.
  keymgr_dpe_sideload_status_e kmac_sideload_status;
  keymgr_dpe_env_pkg::key_shares_t kmac_sideload_key_shares;

  // use `string` here is to combine both internal key and sideload keys, so it could be "internal"
  // or any name at keymgr_key_dest_e
  keymgr_dpe_env_pkg::key_shares_t keys_a_array[
    keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e][string];

  // set this flag when design enters init state, edn req will start periodically
  bit start_edn_req;
  // keymgr_dpe will request edn twice for 64 bit data each time,
  // use this to indicate if it's first or
  // second req. 0: wait for 1st req, 1: for 2nd
  bit edn_req_cnt;
  bit edn_wait_cnt_incr;
  bit edn_wait_cnt_clr;
  int edn_wait_cnt;
  int edn_interval;
  // synchronize req/ack from async domain
  bit edn_req_sync;
  bit edn_req_ack_sync;
  bit edn_req_ack_sync_done;
  bit edn_req_ack_sync_done_qq;

  // If we need to wait for internal signal to be certain value, we may not be able to get that
  // when the sim is close to end. Define a cnt and MaxWaitCycle to avoid sim hang
  int cnt_to_wait_for_internal_value;
  localparam int MaxWaitCycle = 100_000;

  // Disable the check when we force internal design as it's hard to predict design behavior when
  // internal FSM is changed or internal error is triggered
  bit en_chk = 1;

  string msg_id = "keymgr_dpe_if";

  int edn_tolerance_upd = 20;

  // assigned from the keymgr_dpe.keymgr_dpe_ctrl.key_slots_q signal, which should hold the
  // current value of the keyslots in the dut.
  keymgr_dpe_pkg::keymgr_dpe_slot_t [keymgr_dpe_pkg::DpeNumSlots-1:0] internal_key_slots;

  parameter bit UseOtpSeedsInsteadOfFlash = 1;

  task automatic init(bit rand_otp_key, bit invalid_otp_key);
    // Keymgr_dpe only latches OTP key once, so this scb does not support change OTP key on the
    // fly. Will write a direct sequence to cover otp key change on the fly.
    otp_ctrl_pkg::otp_keymgr_key_t local_otp_key;

    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);
    keymgr_dpe_en = lc_ctrl_pkg::On;
    keymgr_dpe_div = 64'h5CFBD765CE33F34E;
    otp_device_id = 'hF0F0;
    otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    flash   = flash_ctrl_pkg::KEYMGR_FLASH_DEFAULT;
    for (int i = 0; i < NumRomDigestInputs; ++i) begin
      rom_digests[i].data = 256'hA20A046CF42E6EAC560A3F82BFA76285B5C1D4AEA7C915E49A32D1C89BE0F507;
      rom_digests[i].valid = '1;
    end
    if (rand_otp_key) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_key,
                                         local_otp_key.creator_root_key_share0_valid == 1;
                                         local_otp_key.creator_root_key_share1_valid == 1;
                                         !(local_otp_key.creator_root_key_share0 inside {0, '1});
                                         !(local_otp_key.creator_root_key_share1 inside {0, '1});
                                         , , msg_id)
    end else begin
      local_otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    end
    if (invalid_otp_key) begin
      local_otp_key.creator_root_key_share0_valid = 0;
      local_otp_key.creator_root_key_share1_valid = 0;
    end
    otp_key = local_otp_key;
  endtask

  // reset local exp variables when reset is issued
  function automatic void reset();
    keymgr_dpe_en = lc_ctrl_pkg::lc_tx_t'($urandom);
    kmac_key_exp = '0;
    aes_key_exp  = '0;
    otbn_key_exp = '0;
    is_kmac_key_good = 0;
    is_kmac_data_good = 0;
    kmac_sideload_status = SideLoadNotAvail;
    aes_sideload_status = SideLoadNotAvail;
    otbn_sideload_status = SideLoadNotAvail;

    // edn related
    edn_interval  = 'h100;
    start_edn_req = 0;
  endfunction

  // Set the keymgr_dpe_div signal to a random value.
  // If is_invalid is true, this value is constrained
  // to be all-zero or all-one.
  function automatic void set_random_keymgr_dpe_div(bit is_invalid);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(keymgr_dpe_div, !(keymgr_dpe_div inside {0, '1});, , msg_id)
    if (is_invalid) begin
      keymgr_dpe_div = ($urandom & 1) ? '0 : '1;
    end
  endfunction

  // Set the otp_device_id signal to a random value. If is_invalid is true, this value is
  // constrained to be all-zero or all-one.
  function automatic void set_random_otp_device_id(bit is_invalid);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(otp_device_id, !(otp_device_id inside {0, '1});, , msg_id)
    if (is_invalid) begin
      otp_device_id = ($urandom & 1) ? '0 : '1;
    end
  endfunction

  // Set the flash signal to a random value. This signal will contain up to num_bad_seeds seeds
  // which are constained to be all-zero or all-one.
  function automatic void set_random_flash(int num_bad_seeds);
    // Start by picking non-constant seeds
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash,
                                       foreach (flash.seeds[i]) {
                                         !(flash.seeds[i] inside {0, '1});
                                       }, , msg_id)
    // If num_bad_seeds is positive, set some randomly chosen seeds to be '0 or '1
    repeat (num_bad_seeds) begin
      int i = $urandom % flash_ctrl_pkg::NumSeeds;
      flash.seeds[i]  = ($urandom & 1) ? '0 : '1;
    end
  endfunction

  // Set the rom digest signal from rom_ctrl i to a random value. If bad_data is true, the digest
  // data will be '0 or '1. If bad_valid is true, the valid signal will be 0.
  function automatic void set_random_rom_digest(int i, bit bad_data, bit bad_valid);
    bit [255:0] data;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data, !(data inside {0, '1});, , msg_id)
    rom_digests[i].data = data;
    if (bad_data) begin
      rom_digests[i].data  = ($urandom & 1) ? '0 : '1;
    end
    rom_digests[i].valid = !bad_valid;
  endfunction

  // randomize lc, flash input data
  task automatic drive_random_hw_input_data(int num_invalid_input = 0);
    // Firstly, decide which signals should be driven with invalid data. Store the choices we make
    // as a set of flags / counters.
    bit bad_keymgr_dpe_div = 1'b0;
    bit bad_otp_device_id = 1'b0;
    int bad_flash_seeds = 0;
    bit [NumRomDigestInputs-1:0] bad_rom_data = '0, bad_rom_valid = '0;

    repeat (num_invalid_input) begin
      randcase
        1: bad_keymgr_dpe_div = 1'b1;
        1: bad_otp_device_id = 1'b1;
        1: bad_flash_seeds++;
        1: bad_rom_data[$urandom % NumRomDigestInputs] = 1'b1;
        1: bad_rom_valid[$urandom % NumRomDigestInputs] = 1'b1;
      endcase
    end

    // Drive each signal, starting each signal's drive at a randomised time, not synchronised with
    // any clock. This models the fact that the signals are from different clock domains.
    fork
      // keymgr_dpe_div
      begin
        #($urandom_range(1000, 0) * 1ns);
        set_random_keymgr_dpe_div(bad_keymgr_dpe_div);
      end

      // otp_device_id
      begin
        #($urandom_range(1000, 0) * 1ns);
        set_random_otp_device_id(bad_otp_device_id);
      end

      // flash
      begin
        #($urandom_range(1000, 0) * 1ns);
        set_random_flash(bad_flash_seeds);
      end

      // rom_digests
      begin
        for (int i = 0; i < NumRomDigestInputs; i++)
          fork
            automatic int local_i = i;
            #($urandom_range(1000, 0) * 1ns);
            set_random_rom_digest(local_i, bad_rom_data[local_i], bad_rom_valid[local_i]);
          join_none
        wait fork;
      end
    join

    // Once the join above has completed, every signal has been driven. Wait a few more cycles for
    // the design to sync up these inputs before we start operations
    repeat ($urandom_range(3, 100)) @(posedge clk);
  endtask

  function automatic void compare_internal_key_slot(
    keymgr_dpe_pkg::keymgr_dpe_slot_t dst_key_slot,
    keymgr_dpe_pkg::keymgr_dpe_slot_t src_key_slot,
    keymgr_dpe_pkg::keymgr_dpe_slot_idx_e dst_slot_index,
    keymgr_dpe_pkg::keymgr_dpe_slot_idx_e src_slot_index,
    bit check_parent_retained
  );
    `DV_CHECK_EQ(dst_key_slot, internal_key_slots[dst_slot_index],
            $sformatf("exp_dst_key_slot[%0d] vs internal_key_slot[%0d]",
            dst_slot_index, dst_slot_index), ,
            msg_id)
    // if the parent is supposed to be retained then check that the
    // src slot contains the expected key still
    if(check_parent_retained)
      `DV_CHECK_EQ(src_key_slot, internal_key_slots[src_slot_index],
              $sformatf("exp_src_key_slot[%0d] vs internal_key_slot[%0d]",
              src_slot_index, src_slot_index), ,
              msg_id)
  endfunction

  // update kmac key for comparison during KDF
  function automatic void update_kdf_key(keymgr_dpe_env_pkg::key_shares_t key_shares,
                                         keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e state,
                                         bit good_key, bit good_data);

    kmac_key_exp <= '{1'b1, key_shares};
    is_kmac_key_good <= good_key;
    is_kmac_data_good <= good_data;
  endfunction

  // store internal key once it's available and use to compare if future OP is invalid
  function automatic void store_internal_key(
      keymgr_dpe_env_pkg::key_shares_t key_shares,
      keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e state
    );

    keys_a_array[state]["Internal"] = key_shares;
  endfunction

  // update sideload key for comparison
  // if it's good key, store it to compare for future invalid OP
  function automatic void update_sideload_key(
      keymgr_dpe_env_pkg::kmac_digests_t key_shares,
      keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e state,
      keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::Kmac
  );
    keymgr_dpe_env_pkg::key_shares_t trun_key_shares = {key_shares[1][keymgr_pkg::KeyWidth-1:0],
                                                    key_shares[0][keymgr_pkg::KeyWidth-1:0]};
    case (dest)
      keymgr_pkg::Kmac: begin
        if (kmac_sideload_status != SideLoadClear) begin
          kmac_sideload_status     <= SideLoadAvail;
          kmac_key_exp             <= '{1'b1, trun_key_shares};
          is_kmac_key_good         <= 1;
          kmac_sideload_key_shares <= trun_key_shares;
        end
      end
      keymgr_pkg::Aes: begin
        if (aes_sideload_status != SideLoadClear) begin
          aes_key_exp         <= '{1'b1, trun_key_shares};
          aes_sideload_status <= SideLoadAvail;
        end
      end
      keymgr_pkg::Otbn: begin
        if (otbn_sideload_status != SideLoadClear) begin
          // only otbn uses full 384 bits digest data
          otbn_key_exp         <= '{1'b1, key_shares};
          otbn_sideload_status <= SideLoadAvail;
        end
      end
      default: `uvm_fatal("keymgr_dpe_if", $sformatf("Unexpect dest type %0s", dest.name))
    endcase

    keys_a_array[state][dest.name] = trun_key_shares;
  endfunction

  function automatic void clear_sideload_key(keymgr_pkg::keymgr_sideload_clr_e clear_dest);
    // reset from Clear to NotAvail
    if (kmac_sideload_status == SideLoadClear) kmac_sideload_status <= SideLoadNotAvail;
    if (aes_sideload_status == SideLoadClear)  aes_sideload_status  <= SideLoadNotAvail;
    if (otbn_sideload_status == SideLoadClear) otbn_sideload_status <= SideLoadNotAvail;
    case (clear_dest)
      keymgr_pkg::SideLoadClrIdle: ; // do nothing
      keymgr_pkg::SideLoadClrAes, keymgr_pkg::SideLoadClrKmac, keymgr_pkg::SideLoadClrOtbn: begin
        clear_one_sideload_key(clear_dest);
      end
      // clear all
      default: begin
        clear_one_sideload_key(keymgr_pkg::SideLoadClrAes);
        clear_one_sideload_key(keymgr_pkg::SideLoadClrKmac);
        clear_one_sideload_key(keymgr_pkg::SideLoadClrOtbn);
      end
    endcase
  endfunction

  function automatic void clear_one_sideload_key(keymgr_pkg::keymgr_sideload_clr_e clear_dest);
    case (clear_dest)
      keymgr_pkg::SideLoadClrAes: begin
        aes_sideload_status <= SideLoadClear;
        aes_key_exp.valid <= 0;
      end
      keymgr_pkg::SideLoadClrKmac: begin
        is_kmac_key_good <= 0;
        kmac_key_exp.valid <= 0;
        kmac_sideload_status <= SideLoadClear;
      end
      keymgr_pkg::SideLoadClrOtbn: begin
        otbn_sideload_status <= SideLoadClear;
        otbn_key_exp.valid <= 0;
      end
      default: begin
        `uvm_fatal(msg_id, $sformatf("Unexpected clear_dest %0d", clear_dest))
      end
    endcase
  endfunction

  function automatic bit get_keymgr_dpe_en();
    return keymgr_dpe_en_sync2 === lc_ctrl_pkg::On;
  endfunction

  function automatic void wipe_sideload_keys();
    is_kmac_key_good <= 0;

    aes_key_exp.valid  <= 0;
    kmac_key_exp.valid <= 0;
    otbn_key_exp.valid <= 0;

    aes_sideload_status  <= SideLoadClear;
    kmac_sideload_status <= SideLoadClear;
    otbn_sideload_status <= SideLoadClear;
  endfunction

  function automatic void update_edn_tolerance_upd(int edn_clk, int main_clk);
    if ((main_clk/edn_clk) * 10 > edn_tolerance_upd) edn_tolerance_upd = (main_clk/edn_clk) * 10;
  endfunction

  logic valid_done_window;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      valid_done_window <= 0;
    end else if (kmac_data_req.last) begin
      valid_done_window <= 1;
    end else if (kmac_data_rsp.done) begin
      valid_done_window <= 0;
    end
  end

  localparam int AdvOpIdx = 0;
  localparam int GenOpIdx = 1;
  wire [1:0] op_enables = {tb.dut.u_ctrl.gen_en_o,
                           tb.dut.u_ctrl.adv_en_o};
  kmac_pkg::app_rsp_t invalid_kmac_rsp;
  logic [2:0] force_sideload_valids, pre_sideload_valids;
  logic [keymgr_pkg::CDIs-1:0][keymgr_pkg::Shares-1:0][keymgr_pkg::KeyWidth-1:0]
        force_internal_key, pre_internal_key;
  task automatic inject_fault(keymgr_dpe_fault_inject_type_e fi_type);
    @(posedge clk);
    `uvm_info(msg_id, $sformatf("injecting fault: %s", fi_type.name), UVM_LOW)
    case (fi_type)
      // force more than one force_cmds
      FaultOpNotOnehot: begin
        bit [2:0] force_cmds;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_cmds, $countones(force_cmds) > 1;, , msg_id)
        inject_cmd_err(force_cmds);
      end
      // force an ongoing operation to another one
      FaultOpNotConsistent: begin
        bit [2:0] force_cmds;

        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_cmds,
                                           $countones(force_cmds) == 1;
                                           force_cmds != op_enables;, , msg_id)
        inject_cmd_err(force_cmds);
      end
      FaultOpNotExist: begin
        bit [2:0] force_cmds;

        // this fault occurs when there is no OP
        `DV_CHECK_EQ_FATAL(op_enables, 0, , msg_id)
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_cmds,
                                           $countones(force_cmds) == 1;
                                           // this CM only applies to adv or gen.
                                           force_cmds != op_enables;, , msg_id)
        inject_cmd_err(force_cmds);
      end
      FaultKmacDoneError: begin
        // wait until it's not a valid window to issue done
        `DV_SPINWAIT(
          while (1) begin
            @(negedge clk);
            if (!valid_done_window) break;
          end, , 10_000, // TIMEOUT_NS_
          msg_id
        )
        `DV_CHECK_STD_RANDOMIZE_FATAL(invalid_kmac_rsp, , msg_id)
        // set `done` to 1, force the other fields to a random value to avoid X propagation
        invalid_kmac_rsp.done = 1;
        force tb.keymgr_dpe_kmac_intf.kmac_data_rsp = invalid_kmac_rsp;
        @(negedge clk);
        release tb.keymgr_dpe_kmac_intf.kmac_data_rsp;
      end
      FaultSideloadNotConsistent: begin
        pre_sideload_valids = tb.dut.u_sideload_ctrl.valids;
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_sideload_valids,
                                           // force to a different and non-zero value
                                           force_sideload_valids != pre_sideload_valids;
                                           force_sideload_valids != 0;, , msg_id)
        force tb.dut.u_sideload_ctrl.valids = force_sideload_valids;
        @(posedge clk);

        `DV_WAIT(kmac_data_rsp.done, , 500_000, // TIMEOUT_NS_
                  msg_id)
        @(posedge clk);
        release tb.dut.u_sideload_ctrl.valids;
      end
      FaultKeyIntgError: begin
        // TODO(opentitan-integrated/issues/669):
        // re-evalute this key logic, as key_state_q does not exist
        // in keymgr_dpe

        //pre_internal_key = tb.dut.u_ctrl.key_state_q;
        //// flip up to 2 bits
        //`DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_internal_key,
        //  $countones(force_internal_key) inside {1, 2};, , msg_id)
        //force_internal_key = force_internal_key ^ pre_internal_key;

        //force tb.dut.u_ctrl.key_state_q = force_internal_key;
        //@(posedge clk);

        //if ($urandom_range(0, 1)) begin
        //  force tb.dut.u_ctrl.key_state_q = pre_internal_key;
        //  @(posedge clk);
        //end
        //release tb.dut.u_ctrl.key_state_q;
      end
      default: `uvm_fatal(msg_id, "impossible value")
    endcase
  endtask

  bit [2:0] prev_cmds;
  task automatic inject_cmd_err(bit[2:0] force_cmds);
    prev_cmds = op_enables;
    `uvm_info(msg_id, $sformatf("Force cmd (gen_en/id_en/adv_en) from %3b to %3b",
                                prev_cmds, force_cmds), UVM_LOW)
    // these signals are wires, need force and then release at reset
    if (force_cmds[AdvOpIdx]) force tb.dut.u_ctrl.adv_en_o = 1;
    if (force_cmds[GenOpIdx]) force tb.dut.u_ctrl.gen_en_o = 1;
    // if in current cycle, kmac_data_rsp is unknown, assign it with a random value to
    // avoid X propagation, because forcing *en_o may cause design to read `kmac_data_i`.
    #1ps;
    if ($isunknown(kmac_data_rsp)) begin
      string path = "tb.dut.kmac_data_i";
      `DV_CHECK_STD_RANDOMIZE_FATAL(invalid_kmac_rsp, , msg_id)
      // don't change these control signals, otherwise, handshaking may get stuck
      invalid_kmac_rsp.ready = kmac_data_rsp.ready;
      invalid_kmac_rsp.done = kmac_data_rsp.done;
      // use deposit rather than force, so that the valid can be preserved until next update
      `DV_CHECK_FATAL(uvm_hdl_deposit(path, invalid_kmac_rsp), , msg_id)
    end
    @(posedge clk);

    if ($urandom_range(0, 1)) begin
      if (force_cmds[AdvOpIdx]) force tb.dut.u_ctrl.adv_en_o = prev_cmds[0];
      if (force_cmds[GenOpIdx]) force tb.dut.u_ctrl.gen_en_o = prev_cmds[1];
      @(posedge clk);
    end

    if (force_cmds[AdvOpIdx]) release tb.dut.u_ctrl.adv_en_o;
    if (force_cmds[GenOpIdx]) release tb.dut.u_ctrl.gen_en_o;
  endtask

  bit trigger_force_hw_key_sel;
  for (genvar i = 0; i < 8; i++) begin : gen_force_hw_key_sel
    always @(trigger_force_hw_key_sel) begin
      if (trigger_force_hw_key_sel) begin
        // force to false, in order to try to move HW key to SW output
        force tb.dut.gen_sw_assigns[i].hw_key_sel_buf[0] = prim_mubi_pkg::MuBi4False;
        force tb.dut.gen_sw_assigns[i].hw_key_sel_buf[1] = prim_mubi_pkg::MuBi4False;
      end else begin
        release tb.dut.gen_sw_assigns[i].hw_key_sel_buf;
      end
    end
  end
  task automatic inject_sideload_fault(bit force_hw_key_sel_or_data_en);
    if (force_hw_key_sel_or_data_en) begin
      `uvm_info(msg_id, "force tb.dut.gen_sw_assigns[*].hw_key_sel_buf[*] to MuBi4False", UVM_LOW)
      trigger_force_hw_key_sel = 1;
    end else begin
      `uvm_info(msg_id, "force tb.dut.u_ctrl.u_data_en.data_sw_en_o to 1", UVM_LOW)
      force tb.dut.u_ctrl.u_data_en.data_sw_en_o = 1;
    end
    // force until the transaction is done.
    @(negedge kmac_data_rsp.done);
    if (force_hw_key_sel_or_data_en) begin
      trigger_force_hw_key_sel = 0;
    end else begin
      release tb.dut.u_ctrl.u_data_en.data_sw_en_o;
    end
  endtask

  // Disable h_data stability assertion when keymgr_dpe is in
  // disabled/invalid state or LC turns off as
  // keymgr_dpe will sent constantly changed entropy data to KMAC for KDF operation.
  always_comb begin
    if (!is_kmac_data_good || keymgr_dpe_en_sync1 != lc_ctrl_pkg::On) begin
      $assertoff(0, tb.keymgr_dpe_kmac_intf.req_data_if.H_DataStableWhenValidAndNotReady_A);
    end else begin
      $asserton(0, tb.keymgr_dpe_kmac_intf.req_data_if.H_DataStableWhenValidAndNotReady_A);
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      keymgr_dpe_en_sync1 <= lc_ctrl_pkg::Off;
      keymgr_dpe_en_sync2 <= lc_ctrl_pkg::Off;
    end else begin
      keymgr_dpe_en_sync1 <= keymgr_dpe_en;
      // avoid race condtion in the driver
      keymgr_dpe_en_sync2 <= #1ps keymgr_dpe_en_sync1;
    end
  end

  // if kmac sideload key is available, switch to it after an operation is completed
  // if not available, de-assert valid after done is asserted
  initial begin
    forever begin
      @(posedge clk);
      if (kmac_data_rsp.done) begin
        if (kmac_sideload_status == SideLoadAvail) begin
          kmac_key_exp <= '{1'b1, kmac_sideload_key_shares};
          is_kmac_key_good <= 1;
        end else begin
          kmac_key_exp.valid <= 0;
          is_kmac_key_good   <= 0;
        end
      end // kmac_data_rsp.done
    end // forever
  end

  // check if key is invalid, it should not match to any of the meaningful keys
  initial begin
    fork
      forever begin
        @(kmac_key or is_kmac_key_good);
        // one cycle to sync with clock, one cycle to allow design to clear the key
        repeat (2) @(posedge clk);
        if (!is_kmac_key_good) check_invalid_key(kmac_key, "KMAC");
      end
      forever begin
        @(aes_key or aes_sideload_status);
        // one cycle to sync with clock, one cycle to allow design to clear the key
        repeat (2) @(posedge clk);
        if (aes_sideload_status != SideLoadAvail) check_invalid_key(aes_key, "AES");
      end
      forever begin
        @(otbn_key or otbn_sideload_status);
        // one cycle to sync with clock, one cycle to allow design to clear the key
        repeat (2) @(posedge clk);
        if (otbn_sideload_status != SideLoadAvail) check_invalid_key(otbn_key, "OTBN");
      end
    join
  end

  function automatic void check_invalid_key(keymgr_pkg::hw_key_req_t act_key, string key_name);
    if (rst_n && act_key.valid && en_chk) begin
      foreach (keys_a_array[state, dest]) begin
        `DV_CHECK_CASE_NE({act_key.key[1], act_key.key[0]}, keys_a_array[state][dest],
            $sformatf("%s key at state %s for %s", key_name, state.name, dest), ,
            msg_id)
        // once key is wiped, 2 shares will be wiped to different values
        `DV_CHECK_CASE_NE(act_key.key[1], act_key.key[0],
            $sformatf("%s key at state %s for %s", key_name, state.name, dest), ,
            msg_id)
      end
    end
  endfunction

  // Create a macro to skip checking key values when LC is off or fault error occurs
  `define ASSERT_IFF_KEYMGR_DPE_LEGAL(NAME, SEQ) \
    `ASSERT(NAME, SEQ, clk, !rst_n || keymgr_dpe_en_sync2 != lc_ctrl_pkg::On || !en_chk)

  `ASSERT_IFF_KEYMGR_DPE_LEGAL(
    CheckKmacKey,
    is_kmac_key_good && kmac_key_exp.valid ->
    (kmac_key.key[0] ^ kmac_key.key[1]) ==
    (kmac_key_exp.key[0] ^ kmac_key_exp.key[1])
  )
  `ASSERT_IFF_KEYMGR_DPE_LEGAL(
    CheckKmacKeyValid,
    is_kmac_key_good -> kmac_key_exp.valid == kmac_key.valid
  )

  `ASSERT_IFF_KEYMGR_DPE_LEGAL(
    CheckAesKey,
    aes_sideload_status == SideLoadAvail &&
    aes_key_exp.valid -> aes_key == aes_key_exp
  )

  `ASSERT_IFF_KEYMGR_DPE_LEGAL(
    CheckAesKeyValid,
    aes_sideload_status != SideLoadClear ->
    aes_key_exp.valid == aes_key.valid
  )

  `ASSERT_IFF_KEYMGR_DPE_LEGAL(
    CheckOtbnKey, otbn_sideload_status == SideLoadAvail &&
    otbn_key_exp.valid -> otbn_key == otbn_key_exp
  )
  `ASSERT_IFF_KEYMGR_DPE_LEGAL(
    CheckOtbnKeyValid,
    otbn_sideload_status != SideLoadClear ->
    otbn_key_exp.valid == otbn_key.valid
  )

  // for EDN assertion
  // sync req/ack to core clk domain
  always @(posedge edn_clk or negedge edn_rst_n) begin
    if (!edn_rst_n) begin
      edn_req_sync <= 0;
      edn_req_ack_sync <= 0;
    end else if (edn_req_ack_sync_done) begin
      edn_req_sync <= 0;
      edn_req_ack_sync <= 0;
    end else if (edn_req && !edn_req_sync) begin
      edn_req_sync <= 1;
    end else if (edn_req & edn_ack) begin
      edn_req_ack_sync <= 1;
    end
  end

  // use start_edn_req to skip checking 1st EDN req as it's triggered by advance cmd
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      edn_req_ack_sync_done <= 0;
      start_edn_req <= 0;
    end else if (edn_req_ack_sync && !edn_req_ack_sync_done) begin
      edn_req_ack_sync_done <= 1;
      start_edn_req <= 1;
    end else if (!edn_req_ack_sync) begin
      edn_req_ack_sync_done <= 0;
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      edn_req_ack_sync_done_qq <= 1'b0;
    end else begin
      edn_req_ack_sync_done_qq <= edn_req_ack_sync_done;
    end
  end

  // Increment the counter for PRNG updates happening unless we're waiting for EDN.
  assign edn_wait_cnt_incr = lfsr_en && (!edn_req_sync || (edn_req_sync && edn_req_ack_sync));

  // Clear the counter upon rising edges of the synchronized req_ack_done signal.
  assign edn_wait_cnt_clr = edn_req_ack_sync_done & !edn_req_ack_sync_done_qq;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      edn_wait_cnt <= 0;
    end else if (edn_wait_cnt_clr) begin
      edn_wait_cnt <= 0;
    end else if (edn_wait_cnt_incr) begin
      edn_wait_cnt <= edn_wait_cnt + 1;
    end
  end

  initial begin
    forever begin
      wait(rst_n === 1);
      edn_req_cnt <= 0;
      `DV_SPINWAIT_EXIT(forever begin
                          @(negedge edn_req_ack_sync_done);
                          edn_req_cnt <= edn_req_cnt + 1;
                        end,
                        wait(!rst_n), , msg_id)
    end
  end

  // consider async handshaking and a few PRNG update requests to start the req. allow no more than
  // `edn_tolerance_upd` tolerance error on the cnt.
  // `edn_tolerance_upd` default value is 20, but if the frequency difference between edn and main
  // clock is too big, the testbench will scale it up to a larger value.
  `ASSERT(CheckEdn1stReq, $rose(edn_req_sync) && edn_req_cnt == 0 && start_edn_req |->
          (edn_wait_cnt >= edn_interval) && (edn_wait_cnt - edn_interval < edn_tolerance_upd),
          clk, !rst_n || !en_chk)

  `ASSERT(CheckEdn2ndReq, $rose(edn_req_sync) && edn_req_cnt == 1 |->
          edn_wait_cnt < edn_tolerance_upd,
          clk, !rst_n || !en_chk)

  `undef ASSERT_IFF_KEYMGR_DPE_LEGAL
endinterface
