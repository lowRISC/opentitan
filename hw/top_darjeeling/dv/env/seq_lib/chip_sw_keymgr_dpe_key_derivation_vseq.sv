// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence interacts with the C test (sw/device/tests/sim_dv/keymgr_dpe_key_derivation.c) and
// performs the checks on digest data.  See the comments in the `body` task for a detailed
// description of the test steps.
class chip_sw_keymgr_dpe_key_derivation_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_keymgr_dpe_key_derivation_vseq)

  `uvm_object_new

  typedef bit [keymgr_pkg::AdvDataWidth-1:0]                  adv_data_t;
  typedef bit [kmac_pkg::AppDigestW-1:0]                      digest_t;
  typedef bit [TL_DW-1:0]                                     tl_data_t;
  typedef bit [keymgr_pkg::KeyWidth-1:0]                      key_t;
  typedef key_t [keymgr_pkg::Shares-1:0]                      key_shares_t;
  typedef bit [keymgr_pkg::OtbnKeyWidth-1:0]                  otbn_key_t;
  typedef otbn_key_t [keymgr_pkg::Shares-1:0]                 otbn_key_shares_t;
  typedef tl_data_t [keymgr_dpe_reg_pkg::NumSaltReg-1:0]      salt_t;
  typedef tl_data_t [keymgr_dpe_reg_pkg::NumSwBindingReg-1:0] sw_binding_t;

  typedef struct packed {
    sw_binding_t                           SoftwareBinding;
    key_t                                  HardwareRevisionSeed;
    bit [keymgr_pkg::DevIdWidth-1:0]       DeviceIdentifier;
    bit [keymgr_pkg::HealthStateWidth-1:0] HealthMeasurement;
    key_t                                  Rom1Digest;
    key_t                                  Rom0Digest;
    key_t                                  CreatorSeed;
  } adv_creator_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [(keymgr_pkg::AdvDataWidth - keymgr_pkg::KeyWidth - keymgr_pkg::SwBindingWidth) - 1 : 0]
                 unused;
    sw_binding_t SoftwareBinding;
    key_t        OwnerSeed;
  } adv_owner_data_t;

  typedef struct packed {
    // some portions are unused, which are 0s
    bit [(keymgr_pkg::AdvDataWidth - keymgr_pkg::SwBindingWidth) - 1 : 0]
                 unused;
    sw_binding_t SoftwareBinding;
  } adv_sw_data_t;

  typedef struct packed {
    tl_data_t          KeyVersion;
    salt_t             Salt;
    keymgr_pkg::seed_t HwDestSeed;
    keymgr_pkg::seed_t OutputSeed;
  } gen_data_t;

  localparam int KmacDigestBytes = kmac_pkg::AppDigestW / 8;

  bit lc_at_prod;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    void'($value$plusargs("lc_at_prod=%0d", lc_at_prod));
    if (lc_at_prod) begin
      otp_write_lc_partition_state(cfg.mem_bkdr_util_h[Otp], LcStProd);
    end
  endtask

  virtual task body();
    key_shares_t stage_0_key, stage_1_key, stage_2_key, stage_3_key;

    super.body();

    // Wait for keymgr_dpe to become available and thus have consumed the creator root key (aka UDS)
    // into a boot stage 0 key.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe derived boot stage 0 key",
             "Timed out waiting for keymgr_dpe to derive boot stage 0 key",
             20_000_000 /* 20 ms, longer than default because OT needs to come out of SW reset*/)
    // At this point, exactly one key slot should be valid and that key slot should contain the
    // creator root key and be in boot stage 0.  Verify that this holds.
    begin
      bit valid_found = 1'b0;
      for (int i = 0; i < keymgr_dpe_pkg::DpeNumSlots; i++) begin
        keymgr_dpe_pkg::keymgr_dpe_slot_t slot = get_key_slot(i);
        if (slot.valid) begin
          `DV_CHECK_EQ(valid_found, 1'b0, "Expecting only one valid key slot")
          valid_found = 1'b1;
          `DV_CHECK_EQ(slot.boot_stage, 'd0, "Expecting boot stage to be 0")
          stage_0_key = slot.key;
        end
      end
      `DV_CHECK_EQ(valid_found, 1'b1, "Expecting one valid key slot")
      `DV_CHECK_EQ(stage_0_key, get_otp_root_key(),
                   "Expecting boot stage 0 key to equal creator root key (UDS) from OTP")
    end
    `uvm_info(`gfn, $sformatf("Boot stage 0 key:\n%s", key_shares_str(stage_0_key)), UVM_LOW)

    // Verify that the outputs generated from the boot stage 0 key match the expectation.
    // Note that the values for version and salt must match those passed in SW. (Ideally, we would
    // backdoor-load them into SW to remove the redundancy, but that's no immediate priority.)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated OTBN output from boot stage 0")
    check_generated_output(.key_shares(stage_0_key),
                           // These values must match those passed in SW. (Ideally, we would
                           // backdoor-load them into SW to remove the redundancy, but that's no
                           // immediate priority.)
                           .dest(keymgr_pkg::Otbn),
                           .version('d0),
                           .salt({32'h49379059, 32'hff523992, 32'h75666880, 32'hc0e44716,
                                  32'h999612df, 32'h80f1a9de, 32'h481eae40, 32'h45e2c7f0}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated SW output from boot stage 0")
    check_generated_output(.key_shares(stage_0_key),
                           // These values must match those passed in SW. (Ideally, we would
                           // backdoor-load them into SW to remove the redundancy, but that's no
                           // immediate priority.)
                           .dest(keymgr_pkg::None),
                           .version('d0),
                           .salt({32'h72d5886b, 32'h4e359e52, 32'h0d7ff336, 32'h267773cf,
                                  32'h00c7d10c, 32'h6dea4fb9, 32'h77fa328a, 32'h15779805}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated KMAC output from boot stage 0")
    check_generated_output(.key_shares(stage_0_key),
                           // These values must match those passed in SW. (Ideally, we would
                           // backdoor-load them into SW to remove the redundancy, but that's no
                           // immediate priority.)
                           .dest(keymgr_pkg::Kmac),
                           .version('d0),
                           .salt({32'h78ad5715, 32'h508680d4, 32'hc7f825b2, 32'ha7924b8d,
                                  32'h0906825f, 32'h77cf81a3, 32'hd63d89bd, 32'h88fd3697}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated AES output from boot stage 0")
    check_generated_output(.key_shares(stage_0_key),
                           // These values must match those passed in SW. (Ideally, we would
                           // backdoor-load them into SW to remove the redundancy, but that's no
                           // immediate priority.)
                           .dest(keymgr_pkg::Aes),
                           .version('d0),
                           .salt({32'h945642d9, 32'hfbcbc925, 32'hdb7b0691, 32'hcd973f4d,
                                  32'h278e051d, 32'h0d9f1f0d, 32'h45eff95b, 32'hb1ad6ba7}));

    // Wait for keymgr_dpe to have advanced to boot stage 1 and thus have consumed the associated
    // values (creator seed etc.).
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe derived boot stage 1 key")
    // At this point, exactly one key slot should contain the boot stage 1 key.  Verify that this
    // holds.
    begin
      bit key_found = 1'b0;
      for (int i = 0; i < keymgr_dpe_pkg::DpeNumSlots; i++) begin
        keymgr_dpe_pkg::keymgr_dpe_slot_t slot = get_key_slot(i);
        if (slot.valid && slot.boot_stage == 'd1) begin
          `DV_CHECK_EQ(key_found, 1'b0, "Expecting only one boot stage 1 key")
          key_found = 1'b1;
          stage_1_key = slot.key;
        end
      end
    end
    `uvm_info(`gfn, $sformatf("Boot stage 1 key:\n%s", key_shares_str(stage_1_key)), UVM_LOW)

    // Verify that the key was derived from the creator data as expected.
    check_derived_key(stage_0_key, get_creator_data(), stage_1_key);

    // Verify that the outputs generated from the boot stage 1 key match the expectation.
    // Note that the values for version and salt must match those passed in SW. (Ideally, we would
    // backdoor-load them into SW to remove the redundancy, but that's no immediate priority.)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated KMAC output from boot stage 1")
    check_generated_output(.key_shares(stage_1_key),
                           .dest(keymgr_pkg::Kmac),
                           .version('d0),
                           .salt({32'h6b21d5da, 32'h929ea4f4, 32'heb06038b, 32'hcecba4ea,
                                  32'h8c8e756a, 32'h26691553, 32'h7189202b, 32'h5e560c86}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated AES output from boot stage 1")
    check_generated_output(.key_shares(stage_1_key),
                           .dest(keymgr_pkg::Aes),
                           .version('d1),
                           .salt({32'hcd887c60, 32'hcc40f919, 32'hdd2972b7, 32'h09cdc35f,
                                  32'h3a10980c, 32'h4b38fdec, 32'h3d56d980, 32'h25314e07}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated SW output from boot stage 1")
    check_generated_output(.key_shares(stage_1_key),
                           .dest(keymgr_pkg::None),
                           .version('d2),
                           .salt({32'h72d5886b, 32'h4e359e52, 32'h0d7ff336, 32'h267773cf,
                                  32'h00c7d10c, 32'h6dea4fb9, 32'h77fa328a, 32'h15779805}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated OTBN output from boot stage 1")
    check_generated_output(.key_shares(stage_1_key),
                           .dest(keymgr_pkg::Otbn),
                           .version('d3),
                           .salt({32'h564712d4, 32'h7ab745f5, 32'h5fa8faa9, 32'h77fce728,
                                  32'hffa3fd3c, 32'h876930f2, 32'h593b54d4, 32'ha75e231b}));

    // Wait for keymgr_dpe to have advanced to boot stage 2 and thus have consumed the owner seed
    // and the owner SW binding.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe derived boot stage 2 key")
    // At this point, exactly one key slot should contain the boot stage 2 key.  Verify that this
    // holds.
    begin
      bit key_found = 1'b0;
      for (int i = 0; i < keymgr_dpe_pkg::DpeNumSlots; i++) begin
        keymgr_dpe_pkg::keymgr_dpe_slot_t slot = get_key_slot(i);
        if (slot.valid && slot.boot_stage == 'd2) begin
          `DV_CHECK_EQ(key_found, 1'b0, "Expecting only one boot stage 2 key")
          key_found = 1'b1;
          stage_2_key = slot.key;
        end
      end
    end
    `uvm_info(`gfn, $sformatf("Boot stage 2 key:\n%s", key_shares_str(stage_2_key)), UVM_LOW)

    // Verify that the key was derived from the owner data as expected.
    check_derived_key(stage_1_key, get_owner_data(), stage_2_key);

    // Verify that the outputs generated from the boot stage 2 key match the expectation.
    // Note that the values for version and salt must match those passed in SW. (Ideally, we would
    // backdoor-load them into SW to remove the redundancy, but that's no immediate priority.)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated SW output from boot stage 2")
    check_generated_output(.key_shares(stage_2_key),
                           .dest(keymgr_pkg::None),
                           .version('d0),
                           .salt({32'he1b3f29c, 32'ha3bc4d2a, 32'h458fdc76, 32'h1b1c0c2e,
                                  32'h1a128785, 32'h69ce2d2f, 32'h8a60fd60, 32'h5307745c}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated AES output from boot stage 2")
    check_generated_output(.key_shares(stage_2_key),
                           .dest(keymgr_pkg::Aes),
                           .version('d1),
                           .salt({32'h0f20f37e, 32'hb951b619, 32'hcb815e8d, 32'h77e17fa4,
                                  32'h3074e3db, 32'he7482b04, 32'hed12d4ee, 32'ha34fba3c}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated KMAC output from boot stage 2")
    check_generated_output(.key_shares(stage_2_key),
                           .dest(keymgr_pkg::Kmac),
                           .version('d2),
                           .salt({32'hb31031a3, 32'h59fe6e8e, 32'h4171de6b, 32'ha3f3d397,
                                  32'h7bb7800b, 32'h8f8f8cda, 32'hb697609d, 32'h122eb3b7}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated OTBN output from boot stage 2")
    check_generated_output(.key_shares(stage_2_key),
                           .dest(keymgr_pkg::Otbn),
                           .version('d3),
                           .salt({32'h3f184f9b, 32'hd4af6765, 32'h8abeb221, 32'haae3ca52,
                                  32'h29f7114f, 32'hf5bf3e01, 32'h6a961bc2, 32'hec932d64}));

    // Wait for keymgr_dpe to have advanced to boot stage 3.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe derived boot stage 3 key")
    // At this point, exactly one key slot should contain the boot stage 3 key.  Verify that this
    // holds.
    begin
     bit key_found = 1'b0;
     for (int i = 0; i < keymgr_dpe_pkg::DpeNumSlots; i++) begin
       keymgr_dpe_pkg::keymgr_dpe_slot_t slot = get_key_slot(i);
       if (slot.valid && slot.boot_stage == 'd3) begin
         `DV_CHECK_EQ(key_found, 1'b0, "Expecting only one boot stage 3 key")
         key_found = 1'b1;
         stage_3_key = slot.key;
       end
     end
    end
    `uvm_info(`gfn, $sformatf("Boot stage 3 key:\n%s", key_shares_str(stage_3_key)), UVM_LOW)

    // Verify that the key was derived from software data as expected.
    begin
     // These values must match those passed in SW. (Ideally, we would backdoor-load them into SW
     // to remove the redundancy, but that's no immediate priority.)
     adv_sw_data_t adv_sw_data = '{
         SoftwareBinding: {32'h952b5a35, 32'h28b4520e, 32'h1f310db2, 32'h832b8477,
                           32'h75b81191, 32'h0668dc27, 32'ha226160d, 32'h45790409},
         default: '0
     };
     check_derived_key(stage_2_key, adv_sw_data, stage_3_key);
    end

    // Verify that the outputs generated from the boot stage 3 key match the expectation.
    // Note that the values for version and salt must match those passed in SW. (Ideally, we would
    // backdoor-load them into SW to remove the redundancy, but that's no immediate priority.)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated AES output from boot stage 3")
    check_generated_output(.key_shares(stage_3_key),
                           .dest(keymgr_pkg::Aes),
                           .version(32'h10),
                           .salt({32'h30059d96, 32'h97436d9c, 32'hf539a20a, 32'h6838564e,
                                  32'h74ad4bb7, 32'h78000277, 32'h423025af, 32'h732e53a9}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated OTBN output from boot stage 3")
    check_generated_output(.key_shares(stage_3_key),
                           .dest(keymgr_pkg::Otbn),
                           .version(32'h20),
                           .salt({32'h2cd82d66, 32'h24275e98, 32'he0344ab2, 32'hc048d59e,
                                  32'h139694c3, 32'h0043f9b4, 32'h413a2212, 32'hc2dcfbc8}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated SW output from boot stage 3")
    check_generated_output(.key_shares(stage_3_key),
                           .dest(keymgr_pkg::None),
                           .version(32'h30),
                           .salt({32'h23c20696, 32'hebaf62f0, 32'ha2ff413f, 32'h22d65603,
                                  32'h91155c24, 32'hda1269fc, 32'hc8611986, 32'hf129041f}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated KMAC output from boot stage 3")
    check_generated_output(.key_shares(stage_3_key),
                           .dest(keymgr_pkg::Kmac),
                           .version(32'h40),
                           .salt({32'h06896da3, 32'h9ce2c0da, 32'haa23a965, 32'h108e57ca,
                                  32'hd926d474, 32'hb6ae40fc, 32'ha65d1375, 32'h6ee7be64}));

    // Verify that the additional outputs generated from boot stage 1 and 2 keys, which should still
    // be available, match the expectation.
    // Note that the values for version and salt must match those passed in SW. (Ideally, we would
    // backdoor-load them into SW to remove the redundancy, but that's no immediate priority.)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated SW output from boot stage 1")
    check_generated_output(.key_shares(stage_1_key),
                           .dest(keymgr_pkg::None),
                           .version(32'd42),
                           .salt({32'h2488d617, 32'h99227306, 32'hcd789bc0, 32'h9787039b,
                                  32'h9869544a, 32'hb28b9fc7, 32'h69ab6f9d, 32'hfb11f188}));
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "KeymgrDpe generated OTBN output from boot stage 2")
    check_generated_output(.key_shares(stage_2_key),
                           .dest(keymgr_pkg::Otbn),
                           .version(32'd7),
                           .salt({32'hfa94162c, 32'hd039a40f, 32'hc2b81d98, 32'h999ce18d,
                                  32'hbf8fb838, 32'h589544ce, 32'hee7790c4, 32'h0de6bdcf}));

  endtask

  // Backdoor-read a given keymgr-internal key slot.
  virtual function keymgr_dpe_pkg::keymgr_dpe_slot_t get_key_slot(int unsigned slot_idx);
    string path = $sformatf("tb.dut.top_darjeeling.u_keymgr_dpe.u_ctrl.key_slots_q[%0d]", slot_idx);
    keymgr_dpe_pkg::keymgr_dpe_slot_t result;
    `DV_CHECK_FATAL(uvm_hdl_read(path, result))
    return result;
  endfunction

  // Combine the two shares of a masked key to get an unmasked key.
  virtual function bit [keymgr_pkg::KeyWidth-1:0] get_unmasked_key(key_shares_t two_share_key);
    return two_share_key[0] ^ two_share_key[1];
  endfunction

  // Collect data used as 'message' to derive the creator key (boot stage 1).
  virtual function adv_data_t get_creator_data();
    adv_creator_data_t creator_data;

    // SoftwareBinding must match the value passed in SW. (Ideally, we would backdoor-load it into
    // SW to remove the redundancy, but that's no immediate priority.)
    creator_data.SoftwareBinding = {
        32'h4ec9c6d6, 32'h19f5cff7, 32'h426dc745, 32'hb8a8379d,
        32'he92f76e2, 32'hcb68ff71, 32'haf36e268, 32'hdc96c23d
    };

    // HardwareRevisionSeed is a netlist constant.
    creator_data.HardwareRevisionSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeRevisionSeed;

    // DeviceIdentifier is stored in OTP; (backdoor-)read it from CSRs.
    for (int i = 0; i < keymgr_pkg::DevIdWidth / TL_DW; i++) begin
      uvm_reg_data_t rdata = csr_peek(ral.lc_ctrl_regs.device_id[i]);
      creator_data.DeviceIdentifier[TL_DW * i +: TL_DW] = rdata;
    end
    `uvm_info(`gfn, $sformatf("DeviceIdentifier:\n%s", key_str(creator_data.DeviceIdentifier)),
              UVM_LOW)

    // HealthMeasurement is a life-cycle-dependent netlist constant.
    // TODO: We appear to have more life cycle states now.
    creator_data.HealthMeasurement =
        lc_at_prod ? top_darjeeling_rnd_cnst_pkg::RndCnstLcCtrlLcKeymgrDivProduction
                   : top_darjeeling_rnd_cnst_pkg::RndCnstLcCtrlLcKeymgrDivTestUnlocked;
    `uvm_info(`gfn, $sformatf("HealthMeasurement:\n128'h%032h", creator_data.HealthMeasurement),
              UVM_LOW)

    // Rom{0,1}Digest come from the respective ROM Controller; (backdoor-)read them from CSRs.
    for (int i = 0; i < keymgr_pkg::KeyWidth / TL_DW; i++) begin
      uvm_reg_data_t rdata = csr_peek(ral.rom_ctrl0_regs.digest[i]);
      creator_data.Rom0Digest[TL_DW * i +: TL_DW] = rdata;
      rdata = csr_peek(ral.rom_ctrl1_regs.digest[i]);
      creator_data.Rom1Digest[TL_DW * i +: TL_DW] = rdata;
    end
    `uvm_info(`gfn, $sformatf("Rom0Digest:\n%s", key_str(creator_data.Rom0Digest)), UVM_LOW)
    `uvm_info(`gfn, $sformatf("Rom1Digest:\n%s", key_str(creator_data.Rom1Digest)), UVM_LOW)

    // CreatorSeed is stored in OTP.
    creator_data.CreatorSeed = get_otp_creator_seed();

    return keymgr_pkg::AdvDataWidth'(creator_data);
  endfunction

  // Collect data used as 'message' to derive the owner key (boot stage 2).
  virtual function adv_data_t get_owner_data();
    adv_owner_data_t owner_data;

    // Zero-pad unused bits.
    owner_data.unused = '0;

    // SoftwareBinding must match the value passed in SW. (Ideally, we would backdoor-load it into
    // SW to remove the redundancy, but that's no immediate priority.)
    owner_data.SoftwareBinding = {
        32'h17eae937, 32'h73008c5a, 32'h181b7a2c, 32'h605c8d2f,
        32'h99f93c05, 32'h064b6b7d, 32'h766be38a, 32'hfe7c4f9b
    };

    // OwnerSeed is stored in OTP.
    owner_data.OwnerSeed = get_otp_owner_seed();

    return keymgr_pkg::AdvDataWidth'(owner_data);
  endfunction

  // Read OwnerSeed from OTP via backdoor and descramble it.
  virtual function key_t get_otp_owner_seed();
    key_t otp_owner_seed;
    for (int i = 0; i < otp_ctrl_reg_pkg::OwnerSeedSize / 4; i++) begin
      otp_owner_seed[i * 32 +: 32] =
          cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::OwnerSeedOffset + i * 4);
    end
    `uvm_fatal(`gfn, "OTP Secret3 key required")
    // TODO(#26288): Secret3 present only in Darjeeling.
    //for (int i = 0; i < otp_ctrl_reg_pkg::OwnerSeedSize / 8; i++) begin
    //  otp_owner_seed[i * 64 +: 64] =
    //      otp_scrambler_pkg::descramble_data(otp_owner_seed[i * 64 +: 64],
    //                                         otp_ctrl_part_pkg::Secret3Idx);
    //end
    `uvm_info(`gfn, $sformatf("OwnerSeed:\n%s", key_str(otp_owner_seed)), UVM_LOW)
    return otp_owner_seed;
  endfunction

  // Read CreatorSeed from OTP via backdoor and descramble it.
  virtual function key_t get_otp_creator_seed();
    key_t otp_creator_seed;
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorSeedSize / 4; i++) begin
      otp_creator_seed[i * 32 +: 32] =
          cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorSeedOffset + i * 4);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorSeedSize / 8; i++) begin
      otp_creator_seed[i * 64 +: 64] =
          otp_scrambler_pkg::descramble_data(otp_creator_seed[i * 64 +: 64],
                                             otp_ctrl_part_pkg::Secret2Idx);
    end
    `uvm_info(`gfn, $sformatf("CreatorSeed:\n%s", key_str(otp_creator_seed)), UVM_LOW)
    return otp_creator_seed;
  endfunction

  // Read CreatorRootKey from OTP via backdoor and descramble it.
  virtual function key_shares_t get_otp_root_key();
    key_shares_t otp_root_key;
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare0Size / 4; i++) begin
      otp_root_key[0][i * 32 +: 32] =
          cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorRootKeyShare0Offset + i * 4);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare0Size / 4 / 2; i++) begin
      otp_root_key[0][i * 64 +: 64] =
          otp_scrambler_pkg::descramble_data(otp_root_key[0][i * 64 +: 64],
                                             otp_ctrl_part_pkg::Secret2Idx);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare1Size / 4; i++) begin
      otp_root_key[1][i * 32 +: 32] =
          cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::CreatorRootKeyShare1Offset + i * 4);
    end
    for (int i = 0; i < otp_ctrl_reg_pkg::CreatorRootKeyShare1Size / 4 / 2; i++) begin
      otp_root_key[1][i * 64 +: 64] =
          otp_scrambler_pkg::descramble_data(otp_root_key[1][i * 64 +: 64],
                                             otp_ctrl_part_pkg::Secret2Idx);
    end
    `uvm_info(`gfn, $sformatf("CreatorRootKey:\n%s", key_shares_str(otp_root_key)), UVM_LOW)
    return otp_root_key;
  endfunction

  // Collect data used as 'message' for versioned output key generation.
  virtual function gen_data_t get_gen_data(tl_data_t key_version,
                                           salt_t salt,
                                           keymgr_pkg::keymgr_key_dest_e dest);
    gen_data_t gen_data;

    gen_data.KeyVersion = key_version;
    gen_data.Salt = salt;

    unique case (dest)
      keymgr_pkg::None: begin // SW
        gen_data.HwDestSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeNoneSeed;
        gen_data.OutputSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeSoftOutputSeed;
      end

      keymgr_pkg::Aes: begin // HW -> AES
        gen_data.HwDestSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeAesSeed;
        gen_data.OutputSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeHardOutputSeed;
      end

      keymgr_pkg::Kmac: begin // HW -> KMAC
        gen_data.HwDestSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeKmacSeed;
        gen_data.OutputSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeHardOutputSeed;
      end

      keymgr_pkg::Otbn: begin // HW -> OTBN
        gen_data.HwDestSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeOtbnSeed;
        gen_data.OutputSeed = top_darjeeling_rnd_cnst_pkg::RndCnstKeymgrDpeHardOutputSeed;
      end

      default: `dv_fatal("Illegal destination (DV bug)!")
    endcase

    return gen_data;
  endfunction

  // Check that a given KMAC digest (`act_digest`) matches the expectation for a given key
  // (`kmac_key`) and data bytes (`data_arr`).
  virtual function void check_kmac_digest(key_t     kmac_key,
                                          bit [7:0] data_arr[],
                                          key_t     act_digest);
    `DV_CHECK_EQ(keymgr_pkg::KeyWidth'(get_kmac_digest(kmac_key, data_arr)),
                 act_digest)
  endfunction

  // Same as `check_kmac_digest` but for OTBN, which uses wider values.
  virtual function void check_kmac_otbn_digest(key_t      kmac_key,
                                               bit [7:0]  data_arr[],
                                               otbn_key_t act_digest);
    `DV_CHECK_EQ(keymgr_pkg::OtbnKeyWidth'(get_kmac_digest(kmac_key, data_arr)),
                 act_digest)
  endfunction

  // Compute KMAC digest (with a DPI call) for a given a key and data bytes.
  virtual function digest_t get_kmac_digest(key_t     kmac_key,
                                            bit [7:0] data_arr[]);
    bit [7:0] key_arr[];
    string custom_str = "";
    bit [7:0] digest_arr[KmacDigestBytes];
    bit [kmac_pkg::AppDigestW-1:0] digest;

    {<< byte {key_arr}} = kmac_key;

    digestpp_dpi_pkg::c_dpi_kmac256(data_arr, data_arr.size(),
                                    key_arr, key_arr.size(),
                                    custom_str,
                                    KmacDigestBytes, digest_arr);
    digest  = {<< byte {digest_arr}};

    return digest;
  endfunction

  // Check that a derived key (`act_digest_shares`, in shares) matches the expected outcome of a key
  // derivation operation from the source key (`key_shares`, in shares) given the data to use as
  // message to KMAC (`kmac_data`).
  virtual function void check_derived_key(key_shares_t key_shares,
                                          adv_data_t   kmac_data,
                                          key_shares_t act_digest_shares);
    bit [7:0] data_arr[];
    {<< byte {data_arr}} = kmac_data;
    check_kmac_digest(get_unmasked_key(key_shares), data_arr, get_unmasked_key(act_digest_shares));
  endfunction

  // Check that a generated output matches the expected outcome of a versioned output key generation
  // operation from the source key (`key_shares`, in shares) to the destination (`dest`) given
  // `version` and `salt` to use in the message to KMAC.
  virtual function void check_generated_output(key_shares_t                  key_shares,
                                               keymgr_pkg::keymgr_key_dest_e dest,
                                               tl_data_t                     version,
                                               salt_t                        salt);
    bit [7:0] data_arr[];
    {<< byte {data_arr}} = get_gen_data(.key_version(version), .salt(salt), .dest(dest));
    if (dest == keymgr_pkg::Otbn) begin
      // Outputs generated for OTBN have a different width.
      otbn_key_shares_t output_shares = get_output_otbn();
      check_kmac_otbn_digest(get_unmasked_key(key_shares),
                             data_arr,
                             output_shares[1] ^ output_shares[0]);
    end else begin
      check_kmac_digest(get_unmasked_key(key_shares),
                        data_arr,
                        get_unmasked_key(get_output(.dest(dest))));
    end
  endfunction

  // Backdoor-read the output from keymgr_dpe to SW a given `dest`ination.
  virtual function key_shares_t get_output(keymgr_pkg::keymgr_key_dest_e dest);
    unique case (dest)
      keymgr_pkg::None: return get_sw_output();
      keymgr_pkg::Aes:  return get_hw_output("tb.dut.top_darjeeling.u_keymgr_dpe.aes_key_o");
      keymgr_pkg::Kmac: return get_hw_output("tb.dut.top_darjeeling.u_keymgr_dpe.kmac_key_o");
      keymgr_pkg::Otbn: `dv_fatal("Illegal use of this function; use `get_output_otbn` instead!")
      default: `dv_fatal("Illegal destination (DV bug)!")
    endcase
  endfunction

  // Backdoor-read keymgr_dpe's SW output.
  virtual function key_shares_t get_sw_output();
    key_shares_t key_shares;
    for (int i = 0; i < keymgr_pkg::KeyWidth / TL_DW; i++) begin
      uvm_reg_data_t rdata = csr_peek(ral.keymgr_dpe.sw_share0_output[i]);
      key_shares[0][TL_DW * i +: TL_DW] = rdata;
      rdata = csr_peek(ral.keymgr_dpe.sw_share1_output[i]);
      key_shares[1][TL_DW * i +: TL_DW] = rdata;
    end
    `uvm_info(`gfn, $sformatf("SW Output:\n%s", key_shares_str(key_shares)), UVM_LOW)
    return key_shares;
  endfunction

  // Backdoor-read keymgr_dpe's HW output at a given path.
  virtual function key_shares_t get_hw_output(string path);
    keymgr_pkg::hw_key_req_t hw_key;
    `DV_CHECK_FATAL(uvm_hdl_read(path, hw_key))
    `DV_CHECK_EQ(hw_key.valid, 1, "Expected HW output key to be valid")
    `uvm_info(`gfn, $sformatf("HW Output at %s:\n%s", path, key_shares_str(hw_key.key)), UVM_LOW)
    return hw_key.key;
  endfunction

  virtual function otbn_key_shares_t get_output_otbn();
    string path = "tb.dut.top_darjeeling.u_keymgr_dpe.otbn_key_o";
    keymgr_pkg::otbn_key_req_t otbn_key;
    `DV_CHECK_FATAL(uvm_hdl_read(path, otbn_key))
    `DV_CHECK_EQ(otbn_key.valid, 1, "Expected OTBN output key to be valid")
    `uvm_info(`gfn, $sformatf("HW Output at %s:\n%s", path, otbn_key_shares_str(otbn_key.key)),
              UVM_LOW)
    return otbn_key.key;
  endfunction

  // Format a key.
  virtual function string key_str(key_t key);
    return $sformatf("256'h%064h", key);
  endfunction

  // Format the two shares of a key with a `separator`.
  virtual function string key_shares_str(key_shares_t key_shares, string separator = "\n");
    return $sformatf("%s%s%s", key_str(key_shares[0]), separator, key_str(key_shares[1]));
  endfunction

  // Format two shares of an OTBN key.
  virtual function string otbn_key_shares_str(otbn_key_shares_t shares, string separator = "\n");
    return $sformatf("384'h%096h%s384'h%096h", shares[0], separator, shares[1]);
  endfunction

endclass : chip_sw_keymgr_dpe_key_derivation_vseq
