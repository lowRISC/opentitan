// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// otp_ctrl_dai_lock_vseq is developed to read/write lock DAI interface by partitions, and request
// read/write access to check if correct status and error code is triggered

// Partition's legal range covers offset to digest addresses, dai_rd/dai_wr function will
// randomize the address based on the granularity.
`define PART_ADDR_RANGE(i) \
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - 8)]}

class otp_ctrl_dai_lock_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_dai_lock_vseq)

  `uvm_object_new

  // enable access_err for each cycle
  constraint no_access_err_c {access_locked_parts == 1;}

  constraint num_trans_c {
    num_trans  inside {[1:10]};
    num_dai_op inside {[1:50]};
  }

  // the LC partition is always the last one
  constraint partition_index_c {part_idx inside {[0:LifeCycleIdx]};}

  constraint dai_wr_legal_addr_c {
    if (part_idx == VendorTestIdx) {
      dai_addr inside `PART_ADDR_RANGE(VendorTestIdx);
    }
    if (part_idx == CreatorSwCfgIdx) {
      dai_addr inside `PART_ADDR_RANGE(CreatorSwCfgIdx);
    }
    if (part_idx == OwnerSwCfgIdx) {
      dai_addr inside `PART_ADDR_RANGE(OwnerSwCfgIdx);
    }
    if (part_idx == OwnershipSlotStateIdx) {
      dai_addr inside `PART_ADDR_RANGE(OwnershipSlotStateIdx);
    }
    if (part_idx == RotCreatorAuthIdx) {
      dai_addr inside `PART_ADDR_RANGE(RotCreatorAuthIdx);
    }
    if (part_idx == RotOwnerAuthSlot0Idx) {
      dai_addr inside `PART_ADDR_RANGE(RotOwnerAuthSlot0Idx);
    }
    if (part_idx == RotOwnerAuthSlot1Idx) {
      dai_addr inside `PART_ADDR_RANGE(RotOwnerAuthSlot1Idx);
    }
    if (part_idx == PlatIntegAuthSlot0Idx) {
      dai_addr inside `PART_ADDR_RANGE(PlatIntegAuthSlot0Idx);
    }
    if (part_idx == PlatIntegAuthSlot1Idx) {
      dai_addr inside `PART_ADDR_RANGE(PlatIntegAuthSlot1Idx);
    }
    if (part_idx == PlatOwnerAuthSlot0Idx) {
      dai_addr inside `PART_ADDR_RANGE(PlatOwnerAuthSlot0Idx);
    }
    if (part_idx == PlatOwnerAuthSlot1Idx) {
      dai_addr inside `PART_ADDR_RANGE(PlatOwnerAuthSlot1Idx);
    }
    if (part_idx == PlatOwnerAuthSlot2Idx) {
      dai_addr inside `PART_ADDR_RANGE(PlatOwnerAuthSlot2Idx);
    }
    if (part_idx == PlatOwnerAuthSlot3Idx) {
      dai_addr inside `PART_ADDR_RANGE(PlatOwnerAuthSlot3Idx);
    }
    if (part_idx == ExtNvmIdx) {
      dai_addr inside `PART_ADDR_RANGE(ExtNvmIdx);
    }
    if (part_idx == RomPatchIdx) {
      dai_addr inside `PART_ADDR_RANGE(RomPatchIdx);
    }
    if (part_idx == HwCfg0Idx) {
      dai_addr inside `PART_ADDR_RANGE(HwCfg0Idx);
    }
    if (part_idx == HwCfg1Idx) {
      dai_addr inside `PART_ADDR_RANGE(HwCfg1Idx);
    }
    if (part_idx == Secret0Idx) {
      dai_addr inside `PART_ADDR_RANGE(Secret0Idx);
    }
    if (part_idx == Secret1Idx) {
      dai_addr inside `PART_ADDR_RANGE(Secret1Idx);
    }
    if (part_idx == Secret2Idx) {
      dai_addr inside `PART_ADDR_RANGE(Secret2Idx);
    }
    if (part_idx == Secret3Idx) {
      dai_addr inside `PART_ADDR_RANGE(Secret3Idx);
    }
    if (part_idx == LifeCycleIdx) {
      if (write_unused_addr) {
        dai_addr inside {[PartInfo[LifeCycleIdx].offset : {OTP_ADDR_WIDTH{1'b1}}]};
      } else {
        dai_addr inside `PART_ADDR_RANGE(LifeCycleIdx);
      }
    }
    solve part_idx before dai_addr;
  }

  constraint dai_wr_digests_c {
    {dai_addr[TL_AW-1:2], 2'b0} dist {
      {
        VendorTestDigestOffset,
        CreatorSwCfgDigestOffset,
        OwnerSwCfgDigestOffset,
        RotCreatorAuthDigestOffset,
        RotOwnerAuthSlot0DigestOffset,
        RotOwnerAuthSlot1DigestOffset,
        PlatIntegAuthSlot0DigestOffset,
        PlatIntegAuthSlot1DigestOffset,
        PlatOwnerAuthSlot0DigestOffset,
        PlatOwnerAuthSlot1DigestOffset,
        PlatOwnerAuthSlot2DigestOffset,
        PlatOwnerAuthSlot3DigestOffset,
        RomPatchDigestOffset,
        HwCfg0DigestOffset,
        HwCfg1DigestOffset,
        Secret0DigestOffset,
        Secret1DigestOffset,
        Secret2DigestOffset,
        Secret3DigestOffset
      } :/ 1,
      [VendorTestOffset : '1] :/ 9
    };
  }

  virtual task pre_start();
    super.pre_start();
    is_valid_dai_op = 0;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if ($urandom_range(0, 1)) begin
      cfg.otp_ctrl_vif.drive_lc_creator_seed_sw_rw_en(get_rand_lc_tx_val(.t_weight(0)));
    end
    if ($urandom_range(0, 1)) begin
      cfg.otp_ctrl_vif.drive_lc_owner_seed_sw_rw_en(get_rand_lc_tx_val(.t_weight(0)));
    end
  endtask

endclass

`undef PART_ADDR_RANGE
