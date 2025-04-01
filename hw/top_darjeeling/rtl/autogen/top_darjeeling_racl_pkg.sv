// Copyright lowRISC contributors (OpenTitan project).
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


package top_darjeeling_racl_pkg;
  import top_racl_pkg::*;

  /**
   * RACL groups and policies:
   *   Null
   *     0: ALL_RD_WR
   *     1: ROT_PRIVATE
   *     2: SOC_ROT
   */

  /**
   * Policy selection vector for mbx0
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX0_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX0_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX0_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx1
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX1_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX1_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX1_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx2
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX2_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX2_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX2_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx3
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX3_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX3_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX3_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx4
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX4_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX4_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX4_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx5
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX5_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX5_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX5_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx6
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX6_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX6_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX6_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx_jtag
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX_JTAG_SOC [4] = '{
    RACL_POLICY_SEL_ALL_RD_WR,   // 0 SOC_CONTROL           : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 1 SOC_STATUS            : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR,   // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 0
    RACL_POLICY_SEL_ALL_RD_WR    // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX_JTAG_SOC_WDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX_JTAG_SOC_RDATA =
    RACL_POLICY_SEL_ALL_RD_WR;   // Policy Idx 0

  /**
   * Policy selection vector for mbx_pcie0
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX_PCIE0_SOC [4] = '{
    RACL_POLICY_SEL_SOC_ROT,     // 0 SOC_CONTROL           : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 1 SOC_STATUS            : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT      // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 2
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX_PCIE0_SOC_WDATA =
    RACL_POLICY_SEL_SOC_ROT;     // Policy Idx 2
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX_PCIE0_SOC_RDATA =
    RACL_POLICY_SEL_SOC_ROT;     // Policy Idx 2

  /**
   * Policy selection vector for mbx_pcie1
   *   TLUL interface name: soc
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_MBX_PCIE1_SOC [4] = '{
    RACL_POLICY_SEL_SOC_ROT,     // 0 SOC_CONTROL           : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 1 SOC_STATUS            : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 2 SOC_DOE_INTR_MSG_ADDR : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT      // 3 SOC_DOE_INTR_MSG_DATA : Policy Idx 2
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX_PCIE1_SOC_WDATA =
    RACL_POLICY_SEL_SOC_ROT;     // Policy Idx 2
  parameter racl_policy_sel_t RACL_POLICY_SEL_WIN_MBX_PCIE1_SOC_RDATA =
    RACL_POLICY_SEL_SOC_ROT;     // Policy Idx 2

  /**
   * Policy selection vector for ac_range_check
   *   TLUL interface name: None
   *   RACL group: Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_VEC_AC_RANGE_CHECK [168] = '{
    RACL_POLICY_SEL_SOC_ROT,     //   0 INTR_STATE                    : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   1 INTR_ENABLE                   : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   2 INTR_TEST                     : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   3 ALERT_TEST                    : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   4 ALERT_STATUS                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   5 LOG_CONFIG                    : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   6 LOG_STATUS                    : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   7 LOG_ADDRESS                   : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   8 RANGE_REGWEN_0                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //   9 RANGE_REGWEN_1                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  10 RANGE_REGWEN_2                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  11 RANGE_REGWEN_3                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  12 RANGE_REGWEN_4                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  13 RANGE_REGWEN_5                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  14 RANGE_REGWEN_6                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  15 RANGE_REGWEN_7                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  16 RANGE_REGWEN_8                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  17 RANGE_REGWEN_9                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  18 RANGE_REGWEN_10               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  19 RANGE_REGWEN_11               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  20 RANGE_REGWEN_12               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  21 RANGE_REGWEN_13               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  22 RANGE_REGWEN_14               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  23 RANGE_REGWEN_15               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  24 RANGE_REGWEN_16               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  25 RANGE_REGWEN_17               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  26 RANGE_REGWEN_18               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  27 RANGE_REGWEN_19               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  28 RANGE_REGWEN_20               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  29 RANGE_REGWEN_21               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  30 RANGE_REGWEN_22               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  31 RANGE_REGWEN_23               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  32 RANGE_REGWEN_24               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  33 RANGE_REGWEN_25               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  34 RANGE_REGWEN_26               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  35 RANGE_REGWEN_27               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  36 RANGE_REGWEN_28               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  37 RANGE_REGWEN_29               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  38 RANGE_REGWEN_30               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  39 RANGE_REGWEN_31               : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  40 RANGE_BASE_0                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  41 RANGE_BASE_1                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  42 RANGE_BASE_2                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  43 RANGE_BASE_3                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  44 RANGE_BASE_4                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  45 RANGE_BASE_5                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  46 RANGE_BASE_6                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  47 RANGE_BASE_7                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  48 RANGE_BASE_8                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  49 RANGE_BASE_9                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  50 RANGE_BASE_10                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  51 RANGE_BASE_11                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  52 RANGE_BASE_12                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  53 RANGE_BASE_13                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  54 RANGE_BASE_14                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  55 RANGE_BASE_15                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  56 RANGE_BASE_16                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  57 RANGE_BASE_17                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  58 RANGE_BASE_18                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  59 RANGE_BASE_19                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  60 RANGE_BASE_20                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  61 RANGE_BASE_21                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  62 RANGE_BASE_22                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  63 RANGE_BASE_23                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  64 RANGE_BASE_24                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  65 RANGE_BASE_25                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  66 RANGE_BASE_26                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  67 RANGE_BASE_27                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  68 RANGE_BASE_28                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  69 RANGE_BASE_29                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  70 RANGE_BASE_30                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  71 RANGE_BASE_31                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  72 RANGE_LIMIT_0                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  73 RANGE_LIMIT_1                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  74 RANGE_LIMIT_2                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  75 RANGE_LIMIT_3                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  76 RANGE_LIMIT_4                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  77 RANGE_LIMIT_5                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  78 RANGE_LIMIT_6                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  79 RANGE_LIMIT_7                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  80 RANGE_LIMIT_8                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  81 RANGE_LIMIT_9                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  82 RANGE_LIMIT_10                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  83 RANGE_LIMIT_11                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  84 RANGE_LIMIT_12                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  85 RANGE_LIMIT_13                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  86 RANGE_LIMIT_14                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  87 RANGE_LIMIT_15                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  88 RANGE_LIMIT_16                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  89 RANGE_LIMIT_17                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  90 RANGE_LIMIT_18                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  91 RANGE_LIMIT_19                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  92 RANGE_LIMIT_20                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  93 RANGE_LIMIT_21                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  94 RANGE_LIMIT_22                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  95 RANGE_LIMIT_23                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  96 RANGE_LIMIT_24                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  97 RANGE_LIMIT_25                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  98 RANGE_LIMIT_26                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     //  99 RANGE_LIMIT_27                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 100 RANGE_LIMIT_28                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 101 RANGE_LIMIT_29                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 102 RANGE_LIMIT_30                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 103 RANGE_LIMIT_31                : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 104 RANGE_ATTR_0                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 105 RANGE_ATTR_1                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 106 RANGE_ATTR_2                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 107 RANGE_ATTR_3                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 108 RANGE_ATTR_4                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 109 RANGE_ATTR_5                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 110 RANGE_ATTR_6                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 111 RANGE_ATTR_7                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 112 RANGE_ATTR_8                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 113 RANGE_ATTR_9                  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 114 RANGE_ATTR_10                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 115 RANGE_ATTR_11                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 116 RANGE_ATTR_12                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 117 RANGE_ATTR_13                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 118 RANGE_ATTR_14                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 119 RANGE_ATTR_15                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 120 RANGE_ATTR_16                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 121 RANGE_ATTR_17                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 122 RANGE_ATTR_18                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 123 RANGE_ATTR_19                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 124 RANGE_ATTR_20                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 125 RANGE_ATTR_21                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 126 RANGE_ATTR_22                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 127 RANGE_ATTR_23                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 128 RANGE_ATTR_24                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 129 RANGE_ATTR_25                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 130 RANGE_ATTR_26                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 131 RANGE_ATTR_27                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 132 RANGE_ATTR_28                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 133 RANGE_ATTR_29                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 134 RANGE_ATTR_30                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 135 RANGE_ATTR_31                 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 136 RANGE_RACL_POLICY_SHADOWED_0  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 137 RANGE_RACL_POLICY_SHADOWED_1  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 138 RANGE_RACL_POLICY_SHADOWED_2  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 139 RANGE_RACL_POLICY_SHADOWED_3  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 140 RANGE_RACL_POLICY_SHADOWED_4  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 141 RANGE_RACL_POLICY_SHADOWED_5  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 142 RANGE_RACL_POLICY_SHADOWED_6  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 143 RANGE_RACL_POLICY_SHADOWED_7  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 144 RANGE_RACL_POLICY_SHADOWED_8  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 145 RANGE_RACL_POLICY_SHADOWED_9  : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 146 RANGE_RACL_POLICY_SHADOWED_10 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 147 RANGE_RACL_POLICY_SHADOWED_11 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 148 RANGE_RACL_POLICY_SHADOWED_12 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 149 RANGE_RACL_POLICY_SHADOWED_13 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 150 RANGE_RACL_POLICY_SHADOWED_14 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 151 RANGE_RACL_POLICY_SHADOWED_15 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 152 RANGE_RACL_POLICY_SHADOWED_16 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 153 RANGE_RACL_POLICY_SHADOWED_17 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 154 RANGE_RACL_POLICY_SHADOWED_18 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 155 RANGE_RACL_POLICY_SHADOWED_19 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 156 RANGE_RACL_POLICY_SHADOWED_20 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 157 RANGE_RACL_POLICY_SHADOWED_21 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 158 RANGE_RACL_POLICY_SHADOWED_22 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 159 RANGE_RACL_POLICY_SHADOWED_23 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 160 RANGE_RACL_POLICY_SHADOWED_24 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 161 RANGE_RACL_POLICY_SHADOWED_25 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 162 RANGE_RACL_POLICY_SHADOWED_26 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 163 RANGE_RACL_POLICY_SHADOWED_27 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 164 RANGE_RACL_POLICY_SHADOWED_28 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 165 RANGE_RACL_POLICY_SHADOWED_29 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT,     // 166 RANGE_RACL_POLICY_SHADOWED_30 : Policy Idx 2
    RACL_POLICY_SEL_SOC_ROT      // 167 RANGE_RACL_POLICY_SHADOWED_31 : Policy Idx 2
  };

endpackage
