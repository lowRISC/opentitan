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

  // Enable TLUL error response on RACL denied accesses
  parameter bit ErrorRsp = 1;

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
    racl_role_vec_t write_perm;    // Write permission (upper bits)
    racl_role_vec_t read_perm;     // Read permission (lower bits)
  } racl_policy_t;

  // RACL range used to protect a range of addresses with a RACL policy (e.g., for sram).
  typedef struct packed {
    logic [top_pkg::TL_AW-1:0] base;       // Start address of range
    logic [top_pkg::TL_AW-1:0] limit;      // End address of range (inclusive)
    racl_policy_sel_t          policy_sel; // Policy selector
    logic                      enable;     // 0: Range is disabled, 1: Range is enabled
  } racl_range_t;

  // RACL policy vector for distributing RACL policies from the RACL widget to the subscribing IP
  typedef racl_policy_t [NrRaclPolicies-1:0] racl_policy_vec_t;

  // Default policy vector for unconnected RACL IPs
  parameter racl_policy_vec_t RACL_POLICY_VEC_DEFAULT = '0;

  // Default policy selection range for unconnected RACL IPs
  parameter racl_range_t RACL_RANGE_T_DEFAULT = '0;

  // Default ROT Private read policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_RD = 16'h1;

  // Default ROT Private write policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_WR = 16'h1;

  // RACL information logged in case of a denial
  typedef struct packed {
    logic                      valid;        // Error information is valid
    logic                      overflow;     // Error overflow, More than 1 RACL error at a time
    racl_role_t                racl_role;
    ctn_uid_t                  ctn_uid;
    logic                      read_access;  // 0: Write access, 1: Read access
    logic [top_pkg::TL_AW-1:0] request_address;
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
   * RACL Policy Selectors for group Null
   */
  parameter racl_policy_sel_t RACL_POLICY_SEL_ALL_RD_WR = 0;
  parameter racl_policy_sel_t RACL_POLICY_SEL_ROT_PRIVATE = 1;
  parameter racl_policy_sel_t RACL_POLICY_SEL_SOC_ROT = 2;


endpackage
