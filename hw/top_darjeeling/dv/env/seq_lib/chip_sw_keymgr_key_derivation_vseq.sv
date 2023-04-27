// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence interacts with the C test (sw/device/tests/sim_dv/keymgr_key_derivation.c) and
// performs the checks on digest data
//  - In the SW test, write fixed value to OTP for root_key and write creator and owner
//    seeds in flash. And then roboot the chip.
//  - In the SV sequence, backdoor read Device ID and ROM digest through CSRs.
//  - For HardwareRevisionSecret, use the constant values in design.
//  - Configure the keymgr and advance to `CreatorRootKey` and `OwnerIntermediateKey`.
//  - Check keymgr internal keys after advance operations.
//  - Generate identity / SW output for the Sealing CDI.
//  - KMAC should finish hashing successfully (not visible to SW) and return digest to
//    keymgr.
//  - Verify that the keymgr has received valid output from the KMAC.
//  - Advance to `Disabled` and verify keymgr enters the state successfully.
//  - Generate identity / SW output and ensure these are neither all 1s/0s nor any valid
//    key value, which proves secrets are wiped by entropy value from EDN.
//
//  - For each operation, wait for the interrupt `op_done` to be triggered and check CSR
//    `op_status` is `DONE_SUCCESS`.
class chip_sw_keymgr_key_derivation_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_keymgr_key_derivation_vseq)

  `uvm_object_new

  typedef bit [keymgr_pkg::Shares-1:0][keymgr_pkg::KeyWidth-1:0] key_shares_t;
  typedef bit [keymgr_pkg::Shares-1:0][kmac_pkg::AppDigestW-1:0] kmac_digests_t;

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
    bit [TL_DW-1:0]      KeyVersion;
    bit [keymgr_reg_pkg::NumSaltReg-1:0][TL_DW-1:0] Salt;
    keymgr_pkg::seed_t   KeyID;
    keymgr_pkg::seed_t   SoftwareExportConstant;
  } gen_out_data_t;

  localparam int KmacDigestBytes = kmac_pkg::AppDigestW / 8;

  localparam bit [keymgr_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] CreatorSwBinding = {
      32'h4ec9c6d6, 32'h19f5cff7, 32'h426dc745, 32'hb8a8379d,
      32'he92f76e2, 32'hcb68ff71, 32'haf36e268, 32'hdc96c23d};

  localparam bit [keymgr_reg_pkg::NumSwBindingReg-1:0][TL_DW-1:0] OwnerIntSwBinding = {
      32'h1940ceeb, 32'hf1394d28, 32'hb012ae5e, 32'h23fb480c,
      32'h3195dbfa, 32'hc2f3bbaf, 32'h3f83d390, 32'he4987b39};

  localparam bit [flash_ctrl_pkg::SeedWidth-1:0] CreatorFlashSeeds = {
      32'ha6521d8f, 32'h13a0e876, 32'h1ca1567b, 32'hb4fb0fdf,
      32'h9f89bc56, 32'h4bd127c7, 32'h322288d8, 32'h4e919d54};

  localparam bit [flash_ctrl_pkg::SeedWidth-1:0] OwnerFlashSeeds = {
      32'h4e919d54, 32'h322288d8, 32'h4bd127c7, 32'h9f89bc56,
      32'hb4fb0fdf, 32'h1ca1567b, 32'h13a0e876, 32'ha6521d8f};

  localparam bit [keymgr_reg_pkg::NumSaltReg-1:0][TL_DW-1:0] Salt = {
      32'hde919d54, 32'h322288d8, 32'h4bd127c7, 32'h9f89bc56,
      32'hb4fb0fdf, 32'h1ca1567b, 32'h13a0e876, 32'hb6521d8f};

  localparam bit [31:0] SwKeyVersion = 32'h11;

  localparam gen_out_data_t GenSWOutData = '{
      SwKeyVersion,
      Salt,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrNoneSeed,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrSoftOutputSeed};

  localparam gen_out_data_t GenKmacOutData = '{
      SwKeyVersion,
      Salt,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrKmacSeed,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrHardOutputSeed};

  localparam gen_out_data_t GenAesOutData = '{
      SwKeyVersion,
      Salt,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrAesSeed,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrHardOutputSeed};

  localparam gen_out_data_t GenOtbnOutData = '{
      SwKeyVersion,
      Salt,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrOtbnSeed,
      top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrHardOutputSeed};

  bit lc_at_prod;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    void'($value$plusargs("lc_at_prod=%0d", lc_at_prod));
    if (lc_at_prod) begin
      cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStProd);
    end
  endtask

  virtual task body();
    string path_internal_key = "tb.dut.top_earlgrey.u_keymgr.u_ctrl.key_o.key";
    key_shares_t new_key;
    bit [keymgr_pkg::KeyWidth-1:0] cur_unmasked_key;
    bit [keymgr_pkg::KeyWidth-1:0] new_unmasked_key;
    bit [keymgr_pkg::AdvDataWidth-1:0] creator_data;

    super.body();

    // wait and check Keymgr entered CreatorRootKey State
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Keymgr entered CreatorRootKey State")
    cur_unmasked_key = get_unmasked_key(get_otp_root_key());
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_internal_key))
    `DV_CHECK_FATAL(uvm_hdl_read(path_internal_key, new_key))
    new_unmasked_key = get_unmasked_key(new_key);

    get_creator_data(creator_data);
    check_internal_key(cur_unmasked_key, creator_data, new_unmasked_key);

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Keymgr generated identity at CreatorRootKey State")
    check_gen_id(new_unmasked_key, top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrCreatorIdentitySeed);

    // wait and check Keymgr entered OwnerIntKey State
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Keymgr entered OwnerIntKey State");
    cur_unmasked_key = new_unmasked_key;
    `DV_CHECK_FATAL(uvm_hdl_read(path_internal_key, new_key))
    new_unmasked_key = get_unmasked_key(new_key);

    check_internal_key(cur_unmasked_key, get_owner_int_data(), new_unmasked_key);
    check_op_in_owner_int_state(new_unmasked_key);
  endtask

  virtual task check_op_in_owner_int_state(bit [keymgr_pkg::KeyWidth-1:0] unmasked_key);
    string path_otbn_key = "tb.dut.top_earlgrey.u_keymgr.otbn_key_o";
    bit [keymgr_pkg::KeyWidth-1:0]     exp_digest;
    bit [keymgr_pkg::KeyWidth-1:0]     unused_key;

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Keymgr generated identity at OwnerIntKey State")
    check_gen_id(unmasked_key, top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrOwnerIntIdentitySeed);

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Keymgr generated SW output at OwnerIntKey State")
    get_sw_shares(exp_digest);
    check_gen_out(unmasked_key, GenSWOutData, exp_digest);

    // check 3 sideload interfaces
    check_kmac_sideload(unmasked_key, unused_key);

    check_aes_sideload(unmasked_key, unused_key);

    // otbn sideload key is 384 bit, so it's treated a bit differently
    begin
      keymgr_pkg::otbn_key_req_t otbn_key;
      bit [7:0] data_arr[];
      bit [kmac_pkg::AppDigestW-1:0] unmask_act_key, unmask_exp_key;
      `DV_WAIT(cfg.sw_logger_vif.printed_log ==
            "Keymgr generated HW output for Otbn at OwnerIntKey State")
      `DV_CHECK_FATAL(uvm_hdl_check_path(path_otbn_key))
      `DV_CHECK_FATAL(uvm_hdl_read(path_otbn_key, otbn_key))
      `DV_CHECK_EQ(otbn_key.valid, 1)

      unmask_act_key = otbn_key.key[0] ^ otbn_key.key[1];

      {<< byte {data_arr}} = GenOtbnOutData;
      unmask_exp_key = get_kmac_digest(unmasked_key, data_arr);

      `DV_CHECK_EQ(unmask_act_key, unmask_exp_key)
    end

    // The next operation is disable, and key will be wiped and changed every cycle.
    $assertoff(0, "tb.dut.top_earlgrey.u_kmac.u_kmac_core.KeyDataStable_M");
  endtask

  virtual task check_kmac_sideload(bit [keymgr_pkg::KeyWidth-1:0] unmasked_key,
                                   output bit [keymgr_pkg::KeyWidth-1:0] sideload_kmac_key);
    keymgr_pkg::hw_key_req_t hw_key;
    string path_kmac_key = "tb.dut.top_earlgrey.u_keymgr.kmac_key_o";
    `DV_WAIT(cfg.sw_logger_vif.printed_log ==
          "Keymgr generated HW output for Kmac at OwnerIntKey State")
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_kmac_key))
    `DV_CHECK_FATAL(uvm_hdl_read(path_kmac_key, hw_key))
    `DV_CHECK_EQ(hw_key.valid, 1)
    sideload_kmac_key = get_unmasked_key(hw_key.key);
    check_gen_out(unmasked_key, GenKmacOutData, sideload_kmac_key);
  endtask

  virtual task check_aes_sideload(bit [keymgr_pkg::KeyWidth-1:0] unmasked_key,
                                  output bit [keymgr_pkg::KeyWidth-1:0] sideload_aes_key);
    keymgr_pkg::hw_key_req_t hw_key;
    string path_aes_key = "tb.dut.top_earlgrey.u_keymgr.aes_key_o";
    `DV_WAIT(cfg.sw_logger_vif.printed_log ==
          "Keymgr generated HW output for Aes at OwnerIntKey State")
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_aes_key))
    `DV_CHECK_FATAL(uvm_hdl_read(path_aes_key, hw_key))
    `DV_CHECK_EQ(hw_key.valid, 1)
    sideload_aes_key = get_unmasked_key(hw_key.key);
    check_gen_out(unmasked_key, GenAesOutData, get_unmasked_key(hw_key.key));

  endtask

  virtual function bit [keymgr_pkg::KeyWidth-1:0] get_unmasked_key(key_shares_t two_share_key);
    return two_share_key[0] ^ two_share_key[1];
  endfunction

  // Here is how the CreatorRootKey data are found
  // SoftwareBinding: program fixed value to keymgr CSRs in the C test
  // HardwareRevisionSecret: backdoor read CSRs at ral.lc_ctrl.device_id
  // HealthMeasurement: HW random constant - RndCnstLcCtrlLcKeymgrDivTestDevRma
  // RomDigest:  backdoor read CSRs at ral.rom_ctrl_regs.digest
  // DiversificationKey: program fixed value to flash in the C test
  virtual task get_creator_data(output bit [keymgr_pkg::AdvDataWidth-1:0] creator_data_out);
    adv_creator_data_t creator_data;
    creator_data.SoftwareBinding = CreatorSwBinding;
    creator_data.HardwareRevisionSecret = top_earlgrey_rnd_cnst_pkg::RndCnstKeymgrRevisionSeed;

    for (int i = 0; i < keymgr_pkg::DevIdWidth / TL_DW; i++) begin
      bit [TL_DW-1:0] rdata;
      csr_peek(ral.lc_ctrl.device_id[i], rdata);
      creator_data.DeviceIdentifier[TL_DW * i +: TL_DW] = rdata;
    end
    `uvm_info(`gfn, $sformatf("DeviceIdentifier 0x%0h", creator_data.DeviceIdentifier),
              UVM_LOW)

    // this test uses either PROD or RMA state
    if (lc_at_prod) begin
      creator_data.HealthMeasurement =
          top_earlgrey_rnd_cnst_pkg::RndCnstLcCtrlLcKeymgrDivProduction;
    end else begin
      creator_data.HealthMeasurement =
          top_earlgrey_rnd_cnst_pkg::RndCnstLcCtrlLcKeymgrDivTestDevRma;
    end

    for (int i = 0; i < keymgr_pkg::KeyWidth / TL_DW; i++) begin
      bit [TL_DW-1:0] rdata;
      csr_peek(ral.rom_ctrl_regs.digest[i], rdata);
      creator_data.RomDigest[TL_DW * i +: TL_DW] = rdata;
    end
    `uvm_info(`gfn, $sformatf("RomDigest 0x%0h", creator_data.RomDigest),
              UVM_LOW)

    creator_data.DiversificationKey = CreatorFlashSeeds;
    creator_data_out = keymgr_pkg::AdvDataWidth'(creator_data);
  endtask

  virtual function bit [keymgr_pkg::AdvDataWidth-1:0] get_owner_int_data();
    adv_owner_int_data_t owner_int_data;
    owner_int_data.SoftwareBinding = OwnerIntSwBinding;
    owner_int_data.OwnerRootSecret = OwnerFlashSeeds;

    return keymgr_pkg::AdvDataWidth'(owner_int_data);
  endfunction

  virtual function key_shares_t get_otp_root_key();
    key_shares_t otp_root_key;
    // backdoor read CreatorRootKey and descramble the data
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare0Size / 4; i++) begin
      otp_root_key[0][i * 32 +: 32] = cfg.mem_bkdr_util_h[Otp].read32(
                             otp_ctrl_reg_pkg::CreatorRootKeyShare0Offset + i * 4);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare0Size / 4 / 2; i++) begin
      otp_root_key[0][i * 64 +: 64] = otp_scrambler_pkg::descramble_data(
          otp_root_key[0][i * 64 +: 64], otp_ctrl_part_pkg::Secret2Idx);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare1Size / 4; i++) begin
      otp_root_key[1][i * 32 +: 32] = cfg.mem_bkdr_util_h[Otp].read32(
                             otp_ctrl_reg_pkg::CreatorRootKeyShare1Offset + i * 4);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare1Size / 4 / 2; i++) begin
      otp_root_key[1][i * 64 +: 64] = otp_scrambler_pkg::descramble_data(
          otp_root_key[1][i * 64 +: 64], otp_ctrl_part_pkg::Secret2Idx);
    end
    `uvm_info(`gfn, $sformatf("otp_root_key 0x%0h, 0x%0h", otp_root_key[0], otp_root_key[1]),
              UVM_LOW)
    return otp_root_key;
  endfunction

  // a generic kmac digest check function, allow to enter with any length of kmac data
  virtual function void check_kmac_digest(
      bit [keymgr_pkg::KeyWidth-1:0]     kmac_key,
      bit [7:0]                          data_arr[],
      bit [keymgr_pkg::KeyWidth-1:0]     act_digest);
    bit [kmac_pkg::AppDigestW-1:0] digest;
    bit [keymgr_pkg::KeyWidth-1:0] exp_digest;

    digest  = get_kmac_digest(kmac_key, data_arr);

    // truncate to 256 bits
    exp_digest = keymgr_pkg::KeyWidth'(digest);

    `DV_CHECK_EQ(act_digest, exp_digest)
  endfunction

  // a generic kmac digest check function, allow to enter with any length of kmac data
  virtual function bit[kmac_pkg::AppDigestW-1:0] get_kmac_digest(
      bit [keymgr_pkg::KeyWidth-1:0]     kmac_key,
      bit [7:0]                          data_arr[]);
    bit [7:0] key_arr[];
    string custom_str = ""; // Just use empty string for top-level tests
    bit [7:0] digest_arr[KmacDigestBytes];
    bit [kmac_pkg::AppDigestW-1:0] digest;

    {<< byte {key_arr}}  = kmac_key;

    digestpp_dpi_pkg::c_dpi_kmac256(data_arr, data_arr.size(),
                                    key_arr, key_arr.size(),
                                    custom_str,
                                    KmacDigestBytes, digest_arr);
    digest  = {<< byte {digest_arr}};

    return digest;
  endfunction

  virtual function void check_internal_key(
      bit [keymgr_pkg::KeyWidth-1:0]     kmac_key,
      bit [keymgr_pkg::AdvDataWidth-1:0] kmac_data,
      bit [keymgr_pkg::KeyWidth-1:0]     act_digest);
    bit [7:0] data_arr[];
    {<< byte {data_arr}} = kmac_data;
    check_kmac_digest(kmac_key, data_arr, act_digest);
  endfunction

  virtual task check_gen_id(
      bit [keymgr_pkg::KeyWidth-1:0]     kmac_key,
      bit [keymgr_pkg::IdDataWidth-1:0]  kmac_data);
    bit [7:0] data_arr[];
    bit [keymgr_pkg::KeyWidth-1:0] sw_shares;
    {<< byte {data_arr}} = kmac_data;
    get_sw_shares(sw_shares);
    check_kmac_digest(kmac_key, data_arr, sw_shares);
  endtask

  virtual function void check_gen_out(
      bit [keymgr_pkg::KeyWidth-1:0]     kmac_key,
      bit [keymgr_pkg::GenDataWidth-1:0] kmac_data,
      bit [keymgr_pkg::KeyWidth-1:0]     exp_digest);
    bit [7:0] data_arr[];
    {<< byte {data_arr}} = kmac_data;
    check_kmac_digest(kmac_key, data_arr, exp_digest);
  endfunction

  virtual task get_sw_shares(output bit [keymgr_pkg::KeyWidth-1:0] sw_shares);
    key_shares_t key_shares;
    for (int i = 0; i < keymgr_pkg::KeyWidth / TL_DW; i++) begin
      bit [TL_DW-1:0] rdata;
      csr_peek(ral.keymgr.sw_share0_output[i], rdata);
      key_shares[0][TL_DW * i +: TL_DW] = rdata;
    end
    for (int i = 0; i < keymgr_pkg::KeyWidth / TL_DW; i++) begin
      bit [TL_DW-1:0] rdata;
      csr_peek(ral.keymgr.sw_share1_output[i], rdata);
      key_shares[1][TL_DW * i +: TL_DW] = rdata;
    end
    `uvm_info(`gfn, $sformatf("Read SW shares 0x%0h, 0x%0h", key_shares[0], key_shares[1]),
              UVM_LOW)
    sw_shares = get_unmasked_key(key_shares);
  endtask

endclass : chip_sw_keymgr_key_derivation_vseq
