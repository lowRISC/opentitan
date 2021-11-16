// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package mem_bkdr_util_pkg;
  // dep packages
  import bus_params_pkg::BUS_AW;
  import dv_utils_pkg::uint32_t;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_part_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_scrambler_pkg::*;
  import prim_secded_pkg::*;
  import sram_scrambler_pkg::*;
  import uvm_pkg::*;

  // Represents the various forms of error detection / correction supported.
  typedef enum int {
    ErrDetectionNone = prim_secded_pkg::SecdedNone,
    Ecc_22_16        = prim_secded_pkg::Secded_22_16,
    Ecc_28_22        = prim_secded_pkg::Secded_28_22,
    Ecc_39_32        = prim_secded_pkg::Secded_39_32,
    Ecc_64_57        = prim_secded_pkg::Secded_64_57,
    Ecc_72_64        = prim_secded_pkg::Secded_72_64,
    EccHamming_22_16 = prim_secded_pkg::SecdedHamming_22_16,
    EccHamming_39_32 = prim_secded_pkg::SecdedHamming_39_32,
    EccHamming_72_64 = prim_secded_pkg::SecdedHamming_72_64,
    EccHamming_76_68 = prim_secded_pkg::SecdedHamming_76_68,
    EccInv_22_16        = prim_secded_pkg::SecdedInv_22_16,
    EccInv_28_22        = prim_secded_pkg::SecdedInv_28_22,
    EccInv_39_32        = prim_secded_pkg::SecdedInv_39_32,
    EccInv_64_57        = prim_secded_pkg::SecdedInv_64_57,
    EccInv_72_64        = prim_secded_pkg::SecdedInv_72_64,
    EccInvHamming_22_16 = prim_secded_pkg::SecdedInvHamming_22_16,
    EccInvHamming_39_32 = prim_secded_pkg::SecdedInvHamming_39_32,
    EccInvHamming_72_64 = prim_secded_pkg::SecdedInvHamming_72_64,
    EccInvHamming_76_68 = prim_secded_pkg::SecdedInvHamming_76_68,
    ParityEven,
    ParityOdd
  } err_detection_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // sources
  `include "mem_bkdr_util.sv"

endpackage
