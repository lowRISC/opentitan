// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package flash_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import flash_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint FLASH_CTRL_ADDR_MAP_SIZE = 128;

  // TODO: These might be made into RTL design parameters.
  parameter NUM_FLASH_BANKS = 2;

  // types
  typedef enum int {
    FlashCtrlIntrProgEmpty  = 0,
    FlashCtrlIntrProgLvl    = 1,
    FlashCtrlIntrRdFull     = 2,
    FlashCtrlIntrRdLvl      = 3,
    FlashCtrlIntrOpDone     = 4,
    FlashCtrlIntrOpError    = 5,
    NumFlashCtrlIntr        = 6
  } flash_ctrl_intr_e;

  typedef virtual mem_bkdr_if mem_bkdr_vif;

  // functions

  // package sources
  `include "flash_ctrl_eflash_reg_block.sv"
  `include "flash_ctrl_env_cfg.sv"
  `include "flash_ctrl_env_cov.sv"
  `include "flash_ctrl_virtual_sequencer.sv"
  `include "flash_ctrl_scoreboard.sv"
  `include "flash_ctrl_env.sv"
  `include "flash_ctrl_vseq_list.sv"

endpackage
