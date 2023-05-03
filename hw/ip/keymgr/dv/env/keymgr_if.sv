// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from LC, OTP and flash
interface keymgr_if(input clk, input rst_n);

  import uvm_pkg::*;
  import keymgr_env_pkg::*;

  // Represents the keymgr sideload state for each sideload interface.
  //
  // The initial status is SideLoadNotAvail. After the sideload key is generated, it becomes
  // SideLoadAvail.
  // Status can't be directly changed from SideLoadClear to SideLoadAvail.
  // When status is SideLoadClear due to SIDELOAD_CLEAR programmed, need to write CSR to 0 to reset
  // it so that status is changed to SideLoadNotAvail, then we may set it to SideLoadAvail again
  lc_ctrl_pkg::lc_tx_t            keymgr_en;
  lc_ctrl_pkg::lc_keymgr_div_t    keymgr_div;
  otp_ctrl_pkg::otp_device_id_t   otp_device_id;
  otp_ctrl_pkg::otp_keymgr_key_t  otp_key;
  flash_ctrl_pkg::keymgr_flash_t  flash;
  rom_ctrl_pkg::keymgr_data_t     rom_digest;

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

  // keymgr_en is async, create a sync one for use in scb
  lc_ctrl_pkg::lc_tx_t keymgr_en_sync1, keymgr_en_sync2;

  // indicate if check the key is same as expected or shouldn't match to any meaningful key
  // when a good KDF is ongoing or kmac sideload key is available, this flag is set to 1
  bit is_kmac_key_good;

  // KMAC data is checked in scb, but when keymgr is in disabled/invalid state or LC is off, KMAC
  // data will be driven with constantly changed entropy data, which violate
  // H_DataStableWhenValidAndNotReady_A. Use this flag to disable it
  bit is_kmac_data_good;

  // sideload status
  keymgr_sideload_status_e aes_sideload_status;
  keymgr_sideload_status_e otbn_sideload_status;

  // When kmac sideload key is generated, `kmac_key` becomes valid with the generated digest data.
  // If SW requests keymgr to do another operation, kmac_key will be updated to the internal key
  // to perform a KMAC KDF operation.
  // Once the operation is done, `kmac_key` is expected to switch automatically to the previous KMAC
  // sideload key.
  keymgr_sideload_status_e kmac_sideload_status;
  keymgr_env_pkg::key_shares_t kmac_sideload_key_shares;

  // use `string` here is to combine both internal key and sideload keys, so it could be "internal"
  // or any name at keymgr_key_dest_e
  keymgr_env_pkg::key_shares_t keys_a_array[keymgr_pkg::keymgr_working_state_e][keymgr_cdi_type_e][
                               string];

  // set this flag when design enters init state, edn req will start periodically
  bit start_edn_req;
  // keymgr will request edn twice for 64 bit data each time, use this to indicate if it's first or
  // second req. 0: wait for 1st req, 1: for 2nd
  bit edn_req_cnt;
  int edn_wait_cnt;
  int edn_interval;
  // synchronize req/ack from async domain
  bit edn_req_sync;
  bit edn_req_ack_sync;
  bit edn_req_ack_sync_done;

  // If we need to wait for internal signal to be certain value, we may not be able to get that
  // when the sim is close to end. Define a cnt and MaxWaitCycle to avoid sim hang
  int cnt_to_wait_for_internal_value;
  localparam int MaxWaitCycle = 100_000;

  // Disable the check when we force internal design as it's hard to predict design behavior when
  // internal FSM is changed or internal error is triggered
  bit en_chk = 1;

  string msg_id = "keymgr_if";

  int edn_tolerance_cycs = 20;

  task automatic init(bit rand_otp_key, bit invalid_otp_key);
    // Keymgr only latches OTP key once, so this scb does not support change OTP key on the
    // fly. Will write a direct sequence to cover otp key change on the fly.
    otp_ctrl_pkg::otp_keymgr_key_t local_otp_key;

    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);
    keymgr_en = lc_ctrl_pkg::On;
    keymgr_div = 64'h5CFBD765CE33F34E;
    otp_device_id = 'hF0F0;
    otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    flash   = flash_ctrl_pkg::KEYMGR_FLASH_DEFAULT;
    rom_digest.data = 256'hA20A046CF42E6EAC560A3F82BFA76285B5C1D4AEA7C915E49A32D1C89BE0F507;
    rom_digest.valid = '1;
    if (rand_otp_key) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_key,
                                         local_otp_key.valid == 1;
                                         !(local_otp_key.key_share0 inside {0, '1});
                                         !(local_otp_key.key_share1 inside {0, '1});, , msg_id)
    end else begin
      local_otp_key = otp_ctrl_pkg::OTP_KEYMGR_KEY_DEFAULT;
    end
    if (invalid_otp_key) local_otp_key.valid = 0;
    otp_key = local_otp_key;
  endtask

  // reset local exp variables when reset is issued
  function automatic void reset();
    keymgr_en = lc_ctrl_pkg::lc_tx_t'($urandom);
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

  // randomize lc, flash input data
  task automatic drive_random_hw_input_data(int num_invalid_input = 0);
    lc_ctrl_pkg::lc_keymgr_div_t     local_keymgr_div;
    bit [keymgr_pkg::DevIdWidth-1:0] local_otp_device_id;
    flash_ctrl_pkg::keymgr_flash_t   local_flash;
    rom_ctrl_pkg::keymgr_data_t      local_rom_digest;

    // async delay as these signals are from different clock domain
    #($urandom_range(1000, 0) * 1ns);

    // randomize all data to be non all 0s or 1s
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_keymgr_div,
                                       !(local_keymgr_div inside {0, '1});, , msg_id)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_device_id,
                                       !(local_otp_device_id inside {0, '1});, , msg_id)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_flash,
                                       foreach (local_flash.seeds[i]) {
                                         !(local_flash.seeds[i] inside {0, '1});
                                       }, , msg_id)

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_rom_digest,
                                       local_rom_digest.valid == 1;
                                       !(local_rom_digest.data inside {0, '1});, , msg_id)

    // make HW input to be all 0s or 1s
    repeat (num_invalid_input) begin
      randcase
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_keymgr_div,
                                             local_keymgr_div inside {0, '1};, , msg_id)
        end
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_otp_device_id,
                                             local_otp_device_id inside {0, '1};, , msg_id)
        end
        1: begin
          int idx = $urandom_range(0, flash_ctrl_pkg::NumSeeds - 1);
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_flash,
                                             local_flash.seeds[idx] inside {0, '1};, , msg_id)
        end
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_rom_digest,
                                             !local_rom_digest.valid;, , msg_id)
        end
        1: begin
          `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(local_rom_digest,
                                             local_rom_digest.valid == 1;
                                             local_rom_digest.data inside {0, '1};, , msg_id)
        end
      endcase
    end

    keymgr_div = local_keymgr_div;
    otp_device_id = local_otp_device_id;
    flash   = local_flash;
    rom_digest = local_rom_digest;

    // a few cycles design to sync up these inputs, before we start operations
    repeat ($urandom_range(3, 100)) @(posedge clk);
  endtask

  // update kmac key for comparison during KDF
  function automatic void update_kdf_key(keymgr_env_pkg::key_shares_t key_shares,
                                         keymgr_pkg::keymgr_working_state_e state,
                                         bit good_key, bit good_data);

    kmac_key_exp <= '{1'b1, key_shares};
    is_kmac_key_good <= good_key;
    is_kmac_data_good <= good_data;
  endfunction

  // store internal key once it's available and use to compare if future OP is invalid
  function automatic void store_internal_key(keymgr_env_pkg::key_shares_t key_shares,
                                             keymgr_pkg::keymgr_working_state_e state,
                                             keymgr_cdi_type_e cdi_type);

    keys_a_array[state][cdi_type]["Internal"] = key_shares;
  endfunction

  // update sideload key for comparison
  // if it's good key, store it to compare for future invalid OP
  function automatic void update_sideload_key(keymgr_env_pkg::kmac_digests_t key_shares,
                                              keymgr_pkg::keymgr_working_state_e state,
                                              keymgr_cdi_type_e cdi_type,
                                              keymgr_pkg::keymgr_key_dest_e dest = keymgr_pkg::Kmac
                                              );
    keymgr_env_pkg::key_shares_t trun_key_shares = {key_shares[1][keymgr_pkg::KeyWidth-1:0],
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
      default: `uvm_fatal("keymgr_if", $sformatf("Unexpect dest type %0s", dest.name))
    endcase

    keys_a_array[state][cdi_type][dest.name] = trun_key_shares;
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

  function automatic bit get_keymgr_en();
    return keymgr_en_sync2 === lc_ctrl_pkg::On;
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

  function automatic void update_edn_toleranc_cycs(int edn_clk, int main_clk);
    if ((main_clk/edn_clk) * 10 > edn_tolerance_cycs) edn_tolerance_cycs = (main_clk/edn_clk) * 10;
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
  localparam int IdOpIdx  = 1;
  localparam int GenOpIdx = 2;
  wire [2:0] op_enables = {tb.dut.u_ctrl.gen_en_o, tb.dut.u_ctrl.id_en_o,
                           tb.dut.u_ctrl.adv_en_o};
  kmac_pkg::app_rsp_t invalid_kmac_rsp;
  logic [2:0] force_sideload_valids, pre_sideload_valids;
  logic [keymgr_pkg::CDIs-1:0][keymgr_pkg::Shares-1:0][keymgr_pkg::KeyWidth-1:0]
        force_internal_key, pre_internal_key;
  task automatic inject_fault(keymgr_fault_inject_type_e fi_type);
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
                                           force_cmds[IdOpIdx] == 0;
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
        force tb.keymgr_kmac_intf.kmac_data_rsp = invalid_kmac_rsp;
        @(negedge clk);
        release tb.keymgr_kmac_intf.kmac_data_rsp;
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
        pre_internal_key = tb.dut.u_ctrl.key_state_q;
        // flip up to 2 bits
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(force_internal_key,
                                           $countones(force_internal_key) inside {1, 2};, , msg_id)
        force_internal_key = force_internal_key ^ pre_internal_key;

        force tb.dut.u_ctrl.key_state_q = force_internal_key;
        @(posedge clk);

        if ($urandom_range(0, 1)) begin
          force tb.dut.u_ctrl.key_state_q = pre_internal_key;
          @(posedge clk);
        end
        release tb.dut.u_ctrl.key_state_q;
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
    if (force_cmds[IdOpIdx])  force tb.dut.u_ctrl.id_en_o  = 1;
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
      if (force_cmds[IdOpIdx])  force tb.dut.u_ctrl.id_en_o  = prev_cmds[1];
      if (force_cmds[GenOpIdx]) force tb.dut.u_ctrl.gen_en_o = prev_cmds[2];
      @(posedge clk);
    end

    if (force_cmds[AdvOpIdx]) release tb.dut.u_ctrl.adv_en_o;
    if (force_cmds[IdOpIdx])  release tb.dut.u_ctrl.id_en_o;
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

  // Disable h_data stability assertion when keymgr is in disabled/invalid state or LC turns off as
  // keymgr will sent constantly changed entropy data to KMAC for KDF operation.
  always_comb begin
    if (!is_kmac_data_good || keymgr_en_sync1 != lc_ctrl_pkg::On) begin
      $assertoff(0, tb.keymgr_kmac_intf.req_data_if.H_DataStableWhenValidAndNotReady_A);
    end else begin
      $asserton(0, tb.keymgr_kmac_intf.req_data_if.H_DataStableWhenValidAndNotReady_A);
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      keymgr_en_sync1 <= lc_ctrl_pkg::Off;
      keymgr_en_sync2 <= lc_ctrl_pkg::Off;
    end else begin
      keymgr_en_sync1 <= keymgr_en;
      // avoid race condtion in the driver
      keymgr_en_sync2 <= #1ps keymgr_en_sync1;
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
      foreach (keys_a_array[state, cdi, dest]) begin
        `DV_CHECK_CASE_NE({act_key.key[1], act_key.key[0]}, keys_a_array[state][cdi][dest],
            $sformatf("%s key at state %s for %s %s", key_name, state.name, cdi.name, dest), ,
            msg_id)
        // once key is wiped, 2 shares will be wiped to different values
        `DV_CHECK_CASE_NE(act_key.key[1], act_key.key[0],
            $sformatf("%s key at state %s for %s %s", key_name, state.name, cdi.name, dest), ,
            msg_id)
      end
    end
  endfunction

  // Create a macro to skip checking key values when LC is off or fault error occurs
  `define ASSERT_IFF_KEYMGR_LEGAL(NAME, SEQ) \
    `ASSERT(NAME, SEQ, clk, !rst_n || keymgr_en_sync2 != lc_ctrl_pkg::On || !en_chk)

  `ASSERT_IFF_KEYMGR_LEGAL(CheckKmacKey, is_kmac_key_good && kmac_key_exp.valid ->
                           (kmac_key.key[0] ^ kmac_key.key[1]) ==
                           (kmac_key_exp.key[0] ^ kmac_key_exp.key[1]))
  `ASSERT_IFF_KEYMGR_LEGAL(CheckKmacKeyValid, is_kmac_key_good ->
                           kmac_key_exp.valid == kmac_key.valid)

  `ASSERT_IFF_KEYMGR_LEGAL(CheckAesKey, aes_sideload_status == SideLoadAvail && aes_key_exp.valid ->
                           aes_key == aes_key_exp)
  `ASSERT_IFF_KEYMGR_LEGAL(CheckAesKeyValid, aes_sideload_status != SideLoadClear ->
                           aes_key_exp.valid == aes_key.valid)

  `ASSERT_IFF_KEYMGR_LEGAL(CheckOtbnKey, otbn_sideload_status == SideLoadAvail && otbn_key_exp.valid
                           -> otbn_key == otbn_key_exp)
  `ASSERT_IFF_KEYMGR_LEGAL(CheckOtbnKeyValid, otbn_sideload_status != SideLoadClear ->
                           otbn_key_exp.valid == otbn_key.valid)

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

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      edn_wait_cnt <= 0;
    end else if (!edn_req_sync) begin
      edn_wait_cnt <= edn_wait_cnt + 1;
    end else begin
      edn_wait_cnt <= 0;
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

  // consider async handshaking and a few cycles to start the req. allow no more than
  // `edn_tolerance_cycs` tolerance error on the cnt.
  // `edn_tolerance_cycs` default value is 20, but if the frequency difference between edn and main
  // clock is too big, the testbench will scale it up to a larger value.
  `ASSERT(CheckEdn1stReq, $rose(edn_req_sync) && edn_req_cnt == 0 && start_edn_req |->
          (edn_wait_cnt > edn_interval) && (edn_wait_cnt - edn_interval < edn_tolerance_cycs),
          clk, !rst_n || !en_chk)

  `ASSERT(CheckEdn2ndReq, $rose(edn_req_sync) && edn_req_cnt == 1 |->
          edn_wait_cnt < edn_tolerance_cycs,
          clk, !rst_n || !en_chk)

  `undef ASSERT_IFF_KEYMGR_LEGAL
endinterface
