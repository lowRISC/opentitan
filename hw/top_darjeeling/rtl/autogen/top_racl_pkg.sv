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


package top_racl_pkg;
  // Number of RACL policies used
  parameter int unsigned NrRaclPolicies = 3;

  // RACL Policy selector bits
  parameter int unsigned RaclPolicySelLen = prim_util_pkg::vbits(NrRaclPolicies);

  // RACL Policy selector type
  typedef logic [RaclPolicySelLen-1:0] racl_policy_sel_t;

  // Number of RACL bits transferred
  parameter int unsigned NrRaclBits = 4;

  // Number of CTN UID bits transferred
  parameter int unsigned NrCtnUidBits = 5;

  // RACL role type binary encoded
  typedef logic [NrRaclBits-1:0] racl_role_t;

  // CTN UID assigned the bus originator
  typedef logic [NrCtnUidBits-1:0] ctn_uid_t;

  // RACL permission: A one-hot encoded role vector
  typedef logic [(2**NrRaclBits)-1:0] racl_role_vec_t;

  // RACL policy containing a read and write permission
  typedef struct packed {
    racl_role_vec_t read_perm;
    racl_role_vec_t write_perm;
  } racl_policy_t;

  // RACL policy vector for distributing RACL policies from the RACL widget to the subscribing IP
  typedef racl_policy_t [NrRaclPolicies-1:0] racl_policy_vec_t;

  // Default policy vector for unconnected RACL IPs
  parameter racl_policy_vec_t RACL_POLICY_VEC_DEFAULT = '0;

  typedef struct packed {
    logic [top_pkg::TL_AW-1:0] base;
    logic [top_pkg::TL_AW-1:0] mask;
    racl_policy_sel_t          policy_sel;
  } racl_range_t;

  // Default ROT Private read policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_RD = 16'h1;

  // Default ROT Private write policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_WR = 16'h1;

  // RACL information logged in case of a denial
  typedef struct packed {
    logic       valid;
    racl_role_t racl_role;
    ctn_uid_t   ctn_uid;
    // 0: Write access, 1: Read access
    logic       read_access;
  } racl_error_log_t;

  // Extract RACL role bits from the TLUL reserved user bits
  function automatic racl_role_t tlul_extract_racl_role_bits(logic [tlul_pkg::RsvdWidth-1:0] rsvd);
    // Waive unused bits
    logic unused_rsvd_bits;
    unused_rsvd_bits = ^{rsvd};

    return racl_role_t'(rsvd[8:5]);
  endfunction

  // Extract CTN UID bits from the TLUL reserved user bits
  function automatic ctn_uid_t tlul_extract_ctn_uid_bits(logic [tlul_pkg::RsvdWidth-1:0] rsvd);
    // Waive unused bits
    logic unused_rsvd_bits;
    unused_rsvd_bits = ^{rsvd};

    return ctn_uid_t'(rsvd[4:0]);
  endfunction

  // Build a TLUL reserved user bit vector based on RACL role and CTN UID
  function automatic logic [tlul_pkg::RsvdWidth-1:0] tlul_build_user_rsvd_vec(racl_role_t racl_role,
                                                                              ctn_uid_t ctn_uid);
    logic [tlul_pkg::RsvdWidth-1:0] rsvd;
    rsvd = '0;
    rsvd[8:5] = racl_role;
    rsvd[4:0] = ctn_uid;
    return rsvd;
  endfunction

  /**
   * RACL Roles
   */
  parameter racl_role_t RACL_ROLE_ROT   = 4'h0;
  parameter racl_role_t RACL_ROLE_ROLE1 = 4'h1;
  parameter racl_role_t RACL_ROLE_SOC   = 4'h2;


  /**
   * RACL groups:
   *   Null
   *     ALL_RD_WR   (Idx 0)
   *     ROT_PRIVATE (Idx 1)
   *     SOC_ROT     (Idx 2)
   */

  /**
   * Policy selection vector for mbx0
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           ALL_RD_WR (Idx 0)
   *     SOC_STATUS:            ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_ADDR: ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_DATA: ALL_RD_WR (Idx 0)
   *   Window to policy mapping:
   *     WDATA: ALL_RD_WR (Idx 0)
   *     RDATA: ALL_RD_WR (Idx 0)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX0_SOC [4] = '{
    0, 0, 0, 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX0_SOC_WIN_WDATA = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX0_SOC_WIN_RDATA = 0;

  /**
   * Policy selection vector for mbx1
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           ALL_RD_WR (Idx 0)
   *     SOC_STATUS:            ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_ADDR: ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_DATA: ALL_RD_WR (Idx 0)
   *   Window to policy mapping:
   *     WDATA: ALL_RD_WR (Idx 0)
   *     RDATA: ALL_RD_WR (Idx 0)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX1_SOC [4] = '{
    0, 0, 0, 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX1_SOC_WIN_WDATA = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX1_SOC_WIN_RDATA = 0;

  /**
   * Policy selection vector for mbx2
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           ALL_RD_WR (Idx 0)
   *     SOC_STATUS:            ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_ADDR: ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_DATA: ALL_RD_WR (Idx 0)
   *   Window to policy mapping:
   *     WDATA: ALL_RD_WR (Idx 0)
   *     RDATA: ALL_RD_WR (Idx 0)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX2_SOC [4] = '{
    0, 0, 0, 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX2_SOC_WIN_WDATA = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX2_SOC_WIN_RDATA = 0;

  /**
   * Policy selection vector for mbx4
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           ALL_RD_WR (Idx 0)
   *     SOC_STATUS:            ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_ADDR: ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_DATA: ALL_RD_WR (Idx 0)
   *   Window to policy mapping:
   *     WDATA: ALL_RD_WR (Idx 0)
   *     RDATA: ALL_RD_WR (Idx 0)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX4_SOC [4] = '{
    0, 0, 0, 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX4_SOC_WIN_WDATA = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX4_SOC_WIN_RDATA = 0;

  /**
   * Policy selection vector for mbx5
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           ALL_RD_WR (Idx 0)
   *     SOC_STATUS:            ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_ADDR: ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_DATA: ALL_RD_WR (Idx 0)
   *   Window to policy mapping:
   *     WDATA: ALL_RD_WR (Idx 0)
   *     RDATA: ALL_RD_WR (Idx 0)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX5_SOC [4] = '{
    0, 0, 0, 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX5_SOC_WIN_WDATA = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX5_SOC_WIN_RDATA = 0;

  /**
   * Policy selection vector for mbx_jtag
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           ALL_RD_WR (Idx 0)
   *     SOC_STATUS:            ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_ADDR: ALL_RD_WR (Idx 0)
   *     SOC_DOE_INTR_MSG_DATA: ALL_RD_WR (Idx 0)
   *   Window to policy mapping:
   *     WDATA: ALL_RD_WR (Idx 0)
   *     RDATA: ALL_RD_WR (Idx 0)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_JTAG_SOC [4] = '{
    0, 0, 0, 0
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_JTAG_SOC_WIN_WDATA = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_JTAG_SOC_WIN_RDATA = 0;

  /**
   * Policy selection vector for mbx_pcie0
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           SOC_ROT (Idx 2)
   *     SOC_STATUS:            SOC_ROT (Idx 2)
   *     SOC_DOE_INTR_MSG_ADDR: SOC_ROT (Idx 2)
   *     SOC_DOE_INTR_MSG_DATA: SOC_ROT (Idx 2)
   *   Window to policy mapping:
   *     WDATA: SOC_ROT (Idx 2)
   *     RDATA: SOC_ROT (Idx 2)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_PCIE0_SOC [4] = '{
    2, 2, 2, 2
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_PCIE0_SOC_WIN_WDATA = 2;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_PCIE0_SOC_WIN_RDATA = 2;

  /**
   * Policy selection vector for mbx_pcie1
   *   TLUL interface name: soc
   *   RACL group: Null
   *   Register to policy mapping:
   *     SOC_CONTROL:           SOC_ROT (Idx 2)
   *     SOC_STATUS:            SOC_ROT (Idx 2)
   *     SOC_DOE_INTR_MSG_ADDR: SOC_ROT (Idx 2)
   *     SOC_DOE_INTR_MSG_DATA: SOC_ROT (Idx 2)
   *   Window to policy mapping:
   *     WDATA: SOC_ROT (Idx 2)
   *     RDATA: SOC_ROT (Idx 2)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_PCIE1_SOC [4] = '{
    2, 2, 2, 2
  };
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_PCIE1_SOC_WIN_WDATA = 2;
  parameter racl_policy_sel_t RACL_POLICY_SEL_MBX_PCIE1_SOC_WIN_RDATA = 2;

  /**
   * Policy selection vector for ac_range_check
   *   TLUL interface name: None
   *   RACL group: Null
   *   Register to policy mapping:
   *     INTR_STATE:                    SOC_ROT (Idx 2)
   *     INTR_ENABLE:                   SOC_ROT (Idx 2)
   *     INTR_TEST:                     SOC_ROT (Idx 2)
   *     ALERT_TEST:                    SOC_ROT (Idx 2)
   *     LOG_CONFIG:                    SOC_ROT (Idx 2)
   *     LOG_STATUS:                    SOC_ROT (Idx 2)
   *     LOG_ADDRESS:                   SOC_ROT (Idx 2)
   *     RANGE_REGWEN_0:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_1:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_2:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_3:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_4:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_5:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_6:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_7:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_8:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_9:                SOC_ROT (Idx 2)
   *     RANGE_REGWEN_10:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_11:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_12:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_13:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_14:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_15:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_16:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_17:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_18:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_19:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_20:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_21:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_22:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_23:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_24:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_25:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_26:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_27:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_28:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_29:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_30:               SOC_ROT (Idx 2)
   *     RANGE_REGWEN_31:               SOC_ROT (Idx 2)
   *     RANGE_BASE_0:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_1:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_2:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_3:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_4:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_5:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_6:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_7:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_8:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_9:                  SOC_ROT (Idx 2)
   *     RANGE_BASE_10:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_11:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_12:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_13:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_14:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_15:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_16:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_17:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_18:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_19:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_20:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_21:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_22:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_23:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_24:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_25:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_26:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_27:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_28:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_29:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_30:                 SOC_ROT (Idx 2)
   *     RANGE_BASE_31:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_0:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_1:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_2:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_3:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_4:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_5:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_6:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_7:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_8:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_9:                 SOC_ROT (Idx 2)
   *     RANGE_LIMIT_10:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_11:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_12:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_13:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_14:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_15:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_16:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_17:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_18:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_19:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_20:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_21:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_22:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_23:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_24:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_25:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_26:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_27:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_28:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_29:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_30:                SOC_ROT (Idx 2)
   *     RANGE_LIMIT_31:                SOC_ROT (Idx 2)
   *     RANGE_PERM_0:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_1:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_2:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_3:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_4:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_5:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_6:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_7:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_8:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_9:                  SOC_ROT (Idx 2)
   *     RANGE_PERM_10:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_11:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_12:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_13:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_14:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_15:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_16:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_17:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_18:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_19:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_20:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_21:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_22:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_23:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_24:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_25:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_26:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_27:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_28:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_29:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_30:                 SOC_ROT (Idx 2)
   *     RANGE_PERM_31:                 SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_0:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_1:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_2:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_3:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_4:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_5:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_6:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_7:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_8:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_9:  SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_10: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_11: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_12: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_13: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_14: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_15: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_16: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_17: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_18: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_19: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_20: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_21: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_22: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_23: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_24: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_25: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_26: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_27: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_28: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_29: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_30: SOC_ROT (Idx 2)
   *     RANGE_RACL_POLICY_SHADOWED_31: SOC_ROT (Idx 2)
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_AC_RANGE_CHECK [167] = '{
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2
  };

endpackage
