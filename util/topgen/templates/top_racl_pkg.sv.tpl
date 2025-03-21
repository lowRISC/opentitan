// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<% import textwrap %>\
<% racl_role_vec_len = 2 ** racl_config['nr_role_bits'] %>\

package top_racl_pkg;
  // Number of RACL policies used
  parameter int unsigned NrRaclPolicies = ${racl_config['nr_policies']};

  // RACL Policy selector bits
  parameter int unsigned RaclPolicySelLen = prim_util_pkg::vbits(NrRaclPolicies);

  // RACL Policy selector type
  typedef logic [RaclPolicySelLen-1:0] racl_policy_sel_t;

  // Enable TLUL error response on RACL denied accesses
  parameter bit ErrorRsp = ${int(racl_config['error_response'])};

  // Number of RACL bits transferred
  parameter int unsigned NrRaclBits = ${racl_config['nr_role_bits']};

  // Number of CTN UID bits transferred
  parameter int unsigned NrCtnUidBits = ${racl_config['nr_ctn_uid_bits']};

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
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_RD = ${racl_role_vec_len}'h${f"{racl_config['rot_private_policy_rd']:x}"};

  // Default ROT Private write policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_WR = ${racl_role_vec_len}'h${f"{racl_config['rot_private_policy_wr']:x}"};

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

    return racl_role_t'(rsvd[${racl_config['role_bit_msb']}:${racl_config['role_bit_lsb']}]);
  endfunction

  // Extract CTN UID bits from the TLUL reserved user bits
  function automatic ctn_uid_t tlul_extract_ctn_uid_bits(logic [tlul_pkg::RsvdWidth-1:0] rsvd);
    // Waive unused bits
    logic unused_rsvd_bits;
    unused_rsvd_bits = ^{rsvd};

    return ctn_uid_t'(rsvd[${racl_config['ctn_uid_bit_msb']}:${racl_config['ctn_uid_bit_lsb']}]);
  endfunction
% if racl_config['role_bit_lsb'] > 0 or racl_config['ctn_uid_bit_msb']:

  // Build a TLUL reserved user bit vector based on RACL role and CTN UID
  function automatic logic [tlul_pkg::RsvdWidth-1:0] tlul_build_user_rsvd_vec(racl_role_t racl_role,
                                                                              ctn_uid_t ctn_uid);
    logic [tlul_pkg::RsvdWidth-1:0] rsvd;
    rsvd = '0;
    rsvd[${racl_config['role_bit_msb']}:${racl_config['role_bit_lsb']}] = racl_role;
    rsvd[${racl_config['ctn_uid_bit_msb']}:${racl_config['ctn_uid_bit_lsb']}] = ctn_uid;
    return rsvd;
  endfunction
% endif

% if racl_config.get('roles'):
  /**
   * RACL Roles
   */
<% racl_role_name_len = max((len(name) for name in racl_config.get('roles', {}).keys()), default=0) %>\
  % for racl_role_name, racl_role in racl_config.get('roles', {}).items():
  parameter racl_role_t RACL_ROLE_${racl_role_name.upper().ljust(racl_role_name_len)} = ${racl_config['nr_role_bits']}'h${f"{racl_role['role_id']:x}"};
  % endfor

% endif
% if racl_config.get('policies'):
  % for racl_group, policies in racl_config.get('policies').items():
  /**
   * RACL Policy Selectors for group ${racl_group}
   */
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
    % for policy_idx,policy in enumerate(list(policies)):
<% name = "RACL_POLICY_SEL{}_{}".format(group_suffix,policy['name'].upper()) %>\
  parameter racl_policy_sel_t ${name} = ${policy_idx};
    % endfor
  % endfor

% endif

endpackage
