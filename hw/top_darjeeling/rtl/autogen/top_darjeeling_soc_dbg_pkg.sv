// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047

package top_darjeeling_soc_dbg_pkg;
  /**
   * Peripheral base address for dmi device on lc_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR = 32'h20000;

  /**
   * Peripheral size in bytes for dmi device on lc_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_LC_CTRL_DMI_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for dbg device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_DBG_BASE_ADDR = 32'h0;

  /**
   * Peripheral size in bytes for dbg device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_DBG_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for soc device on mbx_jtag in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR = 32'h1000;

  /**
   * Peripheral size in bytes for soc device on mbx_jtag in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_MBX_JTAG_SOC_SIZE_BYTES = 32'h20;



endpackage
