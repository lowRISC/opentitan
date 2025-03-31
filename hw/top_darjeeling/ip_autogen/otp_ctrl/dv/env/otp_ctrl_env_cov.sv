// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */
class otp_ctrl_unbuf_err_code_cg_wrap;
  // Unbuffered partition can use TLUL interface to read out but cannot write, thus error_code does
  // not have write_blank_err.
  covergroup unbuf_err_code_cg(string name) with function sample(bit [TL_DW-1:0] val);
    option.per_instance = 1;
    option.name         = name;
    err_code_vals: coverpoint val {
      bins no_err              = {OtpNoError};
      bins macro_err           = {OtpMacroError};
      bins ecc_corr_err        = {OtpMacroEccCorrError};
      bins ecc_uncorr_err      = {OtpMacroEccUncorrError};
      bins access_err          = {OtpAccessError};
      bins check_fail          = {OtpCheckFailError};
      bins fsm_err             = {OtpFsmStateError};
      illegal_bins illegal_err = default;
    }
  endgroup

  function new(string name);
    unbuf_err_code_cg = new(name);
  endfunction
endclass

class otp_ctrl_buf_err_code_cg_wrap;
  // Buffered partition must use DAI interface to access partition, so it does not have access_err
  // and write_blank err.
  covergroup buf_err_code_cg(string name) with function sample(bit [TL_DW-1:0] val);
    option.per_instance = 1;
    option.name         = name;
    err_code_vals: coverpoint val {
      bins no_err              = {OtpNoError};
      bins macro_err           = {OtpMacroError};
      bins ecc_corr_err        = {OtpMacroEccCorrError};
      bins ecc_uncorr_err      = {OtpMacroEccUncorrError};
      bins check_fail          = {OtpCheckFailError};
      bins fsm_err             = {OtpFsmStateError};
      illegal_bins illegal_err = default;
    }
  endgroup

  function new(string name);
    buf_err_code_cg = new(name);
  endfunction
endclass

class otp_ctrl_csr_rd_after_alert_cg_wrap;
  // This covergroup samples CSRs being checked (via CSR read) after fatal alert is issued.
  covergroup csr_rd_after_alert_cg(otp_ctrl_core_reg_block ral) with function sample(bit[TL_DW-1:0]
                                                                                     csr_offset);
    read_csr_after_alert_issued: coverpoint csr_offset {
      bins unbuffered_digests  = {
        ral.vendor_test_digest[0].get_offset(),
        ral.vendor_test_digest[1].get_offset(),
        ral.creator_sw_cfg_digest[0].get_offset(),
        ral.creator_sw_cfg_digest[1].get_offset(),
        ral.owner_sw_cfg_digest[0].get_offset(),
        ral.owner_sw_cfg_digest[1].get_offset(),
        ral.rot_creator_auth_digest[0].get_offset(),
        ral.rot_creator_auth_digest[1].get_offset(),
        ral.rot_owner_auth_slot0_digest[0].get_offset(),
        ral.rot_owner_auth_slot0_digest[1].get_offset(),
        ral.rot_owner_auth_slot1_digest[0].get_offset(),
        ral.rot_owner_auth_slot1_digest[1].get_offset(),
        ral.plat_integ_auth_slot0_digest[0].get_offset(),
        ral.plat_integ_auth_slot0_digest[1].get_offset(),
        ral.plat_integ_auth_slot1_digest[0].get_offset(),
        ral.plat_integ_auth_slot1_digest[1].get_offset(),
        ral.plat_owner_auth_slot0_digest[0].get_offset(),
        ral.plat_owner_auth_slot0_digest[1].get_offset(),
        ral.plat_owner_auth_slot1_digest[0].get_offset(),
        ral.plat_owner_auth_slot1_digest[1].get_offset(),
        ral.plat_owner_auth_slot2_digest[0].get_offset(),
        ral.plat_owner_auth_slot2_digest[1].get_offset(),
        ral.plat_owner_auth_slot3_digest[0].get_offset(),
        ral.plat_owner_auth_slot3_digest[1].get_offset(),
        ral.rom_patch_digest[0].get_offset(),
        ral.rom_patch_digest[1].get_offset()
      };
      bins hw_digests          = {
        ral.hw_cfg0_digest[0].get_offset(),
        ral.hw_cfg0_digest[1].get_offset(),
        ral.hw_cfg1_digest[0].get_offset(),
        ral.hw_cfg1_digest[1].get_offset()
      };
      bins secret_digests      = {
        ral.secret0_digest[0].get_offset(),
        ral.secret0_digest[1].get_offset(),
        ral.secret1_digest[0].get_offset(),
        ral.secret1_digest[1].get_offset(),
        ral.secret2_digest[0].get_offset(),
        ral.secret2_digest[1].get_offset(),
        ral.secret3_digest[0].get_offset(),
        ral.secret3_digest[1].get_offset()
      };
      bins direct_access_rdata = {
        ral.direct_access_rdata[0].get_offset(),
        ral.direct_access_rdata[1].get_offset()
      };
      bins status              = {
        ral.status.get_offset()
      };
      bins error_code          = {
        ral.err_code[0].get_offset(),
        ral.err_code[1].get_offset(),
        ral.err_code[2].get_offset(),
        ral.err_code[3].get_offset(),
        ral.err_code[4].get_offset(),
        ral.err_code[5].get_offset(),
        ral.err_code[6].get_offset(),
        ral.err_code[7].get_offset(),
        ral.err_code[8].get_offset(),
        ral.err_code[9].get_offset(),
        ral.err_code[10].get_offset(),
        ral.err_code[11].get_offset(),
        ral.err_code[12].get_offset(),
        ral.err_code[13].get_offset(),
        ral.err_code[14].get_offset(),
        ral.err_code[15].get_offset(),
        ral.err_code[16].get_offset(),
        ral.err_code[17].get_offset(),
        ral.err_code[18].get_offset(),
        ral.err_code[19].get_offset(),
        ral.err_code[20].get_offset(),
        ral.err_code[21].get_offset(),
        ral.err_code[22].get_offset(),
        ral.err_code[23].get_offset()
      };
    }
  endgroup

  function new(otp_ctrl_core_reg_block ral);
    csr_rd_after_alert_cg = new(ral);
  endfunction

  function void sample(bit[TL_DW-1:0] csr_offset);
    csr_rd_after_alert_cg.sample(csr_offset);
  endfunction
endclass

class otp_ctrl_unbuf_access_lock_cg_wrap;
  covergroup unbuf_access_lock_cg(string name) with function sample(bit read_lock, bit write_lock,
                                                                    bit is_write);
    option.per_instance = 1;
    option.name         = name;
    read_access_locked:  coverpoint read_lock;
    write_access_locked: coverpoint write_lock;
    operation_type: coverpoint is_write {
      bins write_op = {1};
      bins read_op  = {0};
    }
    unbuf_part_access_cross: cross read_access_locked, write_access_locked, operation_type;
  endgroup

  function new(string name);
    unbuf_access_lock_cg = new(name);
  endfunction

  function void sample(bit read_lock, bit write_lock, bit is_write);
    unbuf_access_lock_cg.sample(read_lock, write_lock, is_write);
  endfunction
endclass

class otp_ctrl_env_cov extends cip_base_env_cov #(.CFG_T(otp_ctrl_env_cfg));
  `uvm_component_utils(otp_ctrl_env_cov)

  // the base class provides the following handles for use:
  // otp_ctrl_env_cfg: cfg

  otp_ctrl_unbuf_err_code_cg_wrap     unbuf_err_code_cg_wrap[NumPartUnbuf];
  otp_ctrl_buf_err_code_cg_wrap       buf_err_code_cg_wrap[NumPartBuf];
  otp_ctrl_csr_rd_after_alert_cg_wrap csr_rd_after_alert_cg_wrap;
  otp_ctrl_unbuf_access_lock_cg_wrap  unbuf_access_lock_cg_wrap[NumPartUnbuf];

  bit_toggle_cg_wrap lc_prog_cg;
  bit_toggle_cg_wrap otbn_req_cg;
  bit_toggle_cg_wrap status_csr_cg[OtpStatusFieldSize];

  // covergroups
  // This covergroup collects different conditions when outputs (hwcfg_o, keymgr_key_o) are checked
  // in scb:
  // - If lc_esc_en is On
  // - If each partition is locked (expect LC)
  covergroup power_on_cg with function sample (bit lc_esc_en, bit[NumPart-2:0] parts_locked);
    lc_esc:          coverpoint lc_esc_en;
    vendor_test_lock: coverpoint parts_locked[0];
    creator_sw_cfg_lock: coverpoint parts_locked[1];
    owner_sw_cfg_lock: coverpoint parts_locked[2];
    ownership_slot_state_lock: coverpoint parts_locked[3];
    rot_creator_auth_lock: coverpoint parts_locked[4];
    rot_owner_auth_slot0_lock: coverpoint parts_locked[5];
    rot_owner_auth_slot1_lock: coverpoint parts_locked[6];
    plat_integ_auth_slot0_lock: coverpoint parts_locked[7];
    plat_integ_auth_slot1_lock: coverpoint parts_locked[8];
    plat_owner_auth_slot0_lock: coverpoint parts_locked[9];
    plat_owner_auth_slot1_lock: coverpoint parts_locked[10];
    plat_owner_auth_slot2_lock: coverpoint parts_locked[11];
    plat_owner_auth_slot3_lock: coverpoint parts_locked[12];
    ext_nvm_lock: coverpoint parts_locked[13];
    rom_patch_lock: coverpoint parts_locked[14];
    hw_cfg0_lock: coverpoint parts_locked[15];
    hw_cfg1_lock: coverpoint parts_locked[16];
    secret0_lock: coverpoint parts_locked[17];
    secret1_lock: coverpoint parts_locked[18];
    secret2_lock: coverpoint parts_locked[19];
    secret3_lock: coverpoint parts_locked[20];
  endgroup

  // This covergroup is sampled only if sram request passed scb check.
  covergroup sram_req_cg with function sample (int index, bit locked);
    sram_index: coverpoint index {
      bins sram_key[NumSramKeyReqSlots]  = {[0:(NumSramKeyReqSlots-1)]};
      illegal_bins il = default;
    }
    secret1_lock: coverpoint locked;
    sram_req_lock_cross: cross sram_index, secret1_lock;
  endgroup

  // This covergroup is sampled only if keymgr output passed scb check.
  covergroup keymgr_o_cg with function sample (bit lc_seed_hw_rd_en, bit locked);
    keymgr_rd_en: coverpoint lc_seed_hw_rd_en;
    // TODO: probably should add all partitions with keymgr material here.
    secret2_lock: coverpoint locked;
    keymgr_output_conditions: cross keymgr_rd_en, secret2_lock;
  endgroup

  // This covergroup samples dai request being issued after fatal alert is issued.
  covergroup req_dai_access_after_alert_cg with function sample(bit [TL_DW-1:0] val);
    req_dai_access_after_alert_issued: coverpoint val {
      bins dai_write  = {DaiWrite};
      bins dai_read   = {DaiRead};
      bins dai_digest = {DaiDigest};
    }
  endgroup

  // This covergroup samples background check being issued after fatal alert is issued.
  covergroup issue_checks_after_alert_cg with function sample(bit [TL_DW-1:0] val);
    issue_checks_after_alert_issued: coverpoint val {
      bins integrity_check   = {1};
      bins consistency_check = {2};
    }
  endgroup

  // This covergroup collects DAI err_code value.
  // DAI access does not have checks, thus no check_fail error.
  covergroup dai_err_code_cg with function sample(bit [TL_DW-1:0] val, int part_idx);
    err_code_vals: coverpoint val {
      bins no_err              = {OtpNoError};
      bins macro_err           = {OtpMacroError};
      bins ecc_corr_err        = {OtpMacroEccCorrError};
      bins ecc_uncorr_err      = {OtpMacroEccUncorrError};
      bins write_blank_err     = {OtpMacroWriteBlankError};
      bins access_err          = {OtpAccessError};
      bins fsm_err             = {OtpFsmStateError};
      illegal_bins illegal_err = default;
    }
    partition: coverpoint part_idx {
      bins vendor_test = {VendorTestIdx};
      bins creator_sw_cfg = {CreatorSwCfgIdx};
      bins owner_sw_cfg = {OwnerSwCfgIdx};
      bins ownership_slot_state = {OwnershipSlotStateIdx};
      bins rot_creator_auth = {RotCreatorAuthIdx};
      bins rot_owner_auth_slot0 = {RotOwnerAuthSlot0Idx};
      bins rot_owner_auth_slot1 = {RotOwnerAuthSlot1Idx};
      bins plat_integ_auth_slot0 = {PlatIntegAuthSlot0Idx};
      bins plat_integ_auth_slot1 = {PlatIntegAuthSlot1Idx};
      bins plat_owner_auth_slot0 = {PlatOwnerAuthSlot0Idx};
      bins plat_owner_auth_slot1 = {PlatOwnerAuthSlot1Idx};
      bins plat_owner_auth_slot2 = {PlatOwnerAuthSlot2Idx};
      bins plat_owner_auth_slot3 = {PlatOwnerAuthSlot3Idx};
      bins ext_nvm = {ExtNvmIdx};
      bins rom_patch = {RomPatchIdx};
      bins hw_cfg0 = {HwCfg0Idx};
      bins hw_cfg1 = {HwCfg1Idx};
      bins secret0 = {Secret0Idx};
      bins secret1 = {Secret1Idx};
      bins secret2 = {Secret2Idx};
      bins secret3 = {Secret3Idx};
      bins life_cycle = {LifeCycleIdx};
      bins illegal_idx    = default;
    }
    // LC partition has a separate LCI err_code to collect macro related errors.
    dai_err_code_for_all_partitions: cross err_code_vals, partition {
      // Illegal bin - vendor_test partition does not have EccUncorrectable error.
      illegal_bins vendor_test_ecc_uncorrectable_err =
                   binsof (partition.vendor_test) && binsof (err_code_vals.ecc_uncorr_err);
      ignore_bins life_cycle_ignore = binsof (partition.life_cycle) &&
                  binsof(err_code_vals) intersect {[OtpMacroError:OtpMacroWriteBlankError]};
    }
  endgroup

  // This covergroup collects LCI err_code value.
  // LCI access does not have digest, thus no access_err. Check_fail, ecc_errors are covered in lc
  // buffered partition instead of LCI here.
  covergroup lci_err_code_cg with function sample(bit [TL_DW-1:0] val);
    err_code_vals: coverpoint val {
      bins no_err              = {OtpNoError};
      bins macro_err           = {OtpMacroError};
      bins write_blank_err     = {OtpMacroWriteBlankError};
      bins fsm_err             = {OtpFsmStateError};
      illegal_bins illegal_err = default;
    }
  endgroup

  covergroup dai_access_secret2_cg with function sample(bit lc_rw_en, dai_cmd_e dai_cmd);
    lc_creator_seed_sw_rw_en: coverpoint lc_rw_en;
    dai_access_cmd: coverpoint dai_cmd {
      bins dai_rd     = {DaiRead};
      bins dai_wr     = {DaiWrite};
      bins dai_digest = {DaiDigest};
    }
    dai_access_secret2: cross lc_creator_seed_sw_rw_en, dai_access_cmd;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // Create coverage from local covergroups.
    power_on_cg                   = new();
    sram_req_cg                   = new();
    keymgr_o_cg                   = new();
    req_dai_access_after_alert_cg = new();
    issue_checks_after_alert_cg   = new();
    dai_err_code_cg               = new();
    lci_err_code_cg               = new();
    dai_access_secret2_cg         = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create instances from bit_toggle_cg_wrapper.
    lc_prog_cg  = new("lc_prog_cg", "", 0);
    otbn_req_cg = new("otbn_req_cg", "", 0);
    foreach (status_csr_cg[i]) begin
      otp_status_e index = otp_status_e'(i);
      status_csr_cg[i]= new(index.name, "status_csr_cg", 0);
    end

    // Create instances from external wrapper classes.
    csr_rd_after_alert_cg_wrap = new(cfg.ral);
    foreach (unbuf_err_code_cg_wrap[i]) begin
      otp_status_e index = otp_status_e'(i);
      unbuf_err_code_cg_wrap[i] = new($sformatf("unbuf_err_code_cg_wrap[%0s]", index.name));
    end
    foreach (buf_err_code_cg_wrap[i]) begin
      otp_status_e index = otp_status_e'(i + 2);
      buf_err_code_cg_wrap[i] = new($sformatf("buf_err_code_cg_wrap[%0s]", index.name));
    end
    foreach (unbuf_access_lock_cg_wrap[i]) begin
      part_idx_e index = part_idx_e'(i);
      unbuf_access_lock_cg_wrap[i] = new($sformatf("buf_err_code_cg_wrap[%0s]", index.name));
    end
  endfunction

  function void collect_status_cov(bit [TL_DW-1:0] val);
    foreach (status_csr_cg[i]) begin
      status_csr_cg[i].sample(val[i]);
    end
  endfunction

  // Collect coverage for err_code when it is a compact multi-reg. For DAI error it uses the given
  // access_part_idx as the target of the DAI access.
  function void collect_compact_err_code_cov(bit [TL_DW-1:0] val, int access_part_idx = DaiIdx);
    dv_base_reg_field err_code_flds[$];
    cfg.ral.err_code[0].get_dv_base_reg_fields(err_code_flds);
    foreach (err_code_flds[part]) begin
      collect_err_code_cov(part, get_field_val(err_code_flds[part], val), access_part_idx);
    end
  endfunction

  // Collect coverage for a given partition error_code. For DAI error it uses the given
  // access_part_idx as the target of the DAI access.
  function void collect_err_code_cov(int part_idx, bit [TL_DW-1:0] val,
                                     int access_part_idx = DaiIdx);
    case (part_idx)
      OtpVendorTestErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpCreatorSwCfgErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpOwnerSwCfgErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpOwnershipSlotStateErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpRotCreatorAuthErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpRotOwnerAuthSlot0ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpRotOwnerAuthSlot1ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpPlatIntegAuthSlot0ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpPlatIntegAuthSlot1ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpPlatOwnerAuthSlot0ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpPlatOwnerAuthSlot1ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpPlatOwnerAuthSlot2ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpPlatOwnerAuthSlot3ErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpExtNvmErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpRomPatchErrIdx: begin
        unbuf_err_code_cg_wrap[part_idx].unbuf_err_code_cg.sample(val);
      end
      OtpHwCfg0ErrIdx: begin
        buf_err_code_cg_wrap[part_idx - NumPartUnbuf].buf_err_code_cg.sample(val);
      end
      OtpHwCfg1ErrIdx: begin
        buf_err_code_cg_wrap[part_idx - NumPartUnbuf].buf_err_code_cg.sample(val);
      end
      OtpSecret0ErrIdx: begin
        buf_err_code_cg_wrap[part_idx - NumPartUnbuf].buf_err_code_cg.sample(val);
      end
      OtpSecret1ErrIdx: begin
        buf_err_code_cg_wrap[part_idx - NumPartUnbuf].buf_err_code_cg.sample(val);
      end
      OtpSecret2ErrIdx: begin
        buf_err_code_cg_wrap[part_idx - NumPartUnbuf].buf_err_code_cg.sample(val);
      end
      OtpSecret3ErrIdx: begin
        buf_err_code_cg_wrap[part_idx - NumPartUnbuf].buf_err_code_cg.sample(val);
      end
      OtpLifeCycleErrIdx: begin
      end
      OtpDaiErrIdx: begin
        dai_err_code_cg.sample(val, access_part_idx);
      end
      OtpLciErrIdx: begin
        lci_err_code_cg.sample(val);
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid err_code index %0d", part_idx))
      end
    endcase
  endfunction
endclass
