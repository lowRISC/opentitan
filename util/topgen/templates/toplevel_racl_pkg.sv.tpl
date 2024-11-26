// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}

package top_racl_pkg;
  // Number of RACL policies used
  parameter int unsigned NrRaclPolicies = ${racl_config['nr_policies']};

  // Number of RACL bits transferred
  parameter int unsigned NrRaclBits = 4;

  // Number of CTN UID bits transferred
  parameter int unsigned NrCtnUidBits = 8;

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

  // RACL information logged in case of a denial
  typedef struct packed {
    racl_role_t racl_role;
    ctn_uid_t   ctn_uid;
    // 0: Write access, 1: Read access
    logic       read_not_write;
  } racl_error_log_t;

  // Extract RACL role bits from the TLUL reserved user bits
  function automatic racl_role_t tlul_extract_racl_role_bits(logic [tlul_pkg::RsvdWidth-1:0] rsvd);
    // Waive unused bits
    logic unused_rsvd_bits;
    unused_rsvd_bits = ^{rsvd};

    return racl_role_t'(rsvd[11:8]);
  endfunction

  // Extract CTN UID bits from the TLUL reserved user bits
  function automatic ctn_uid_t tlul_extract_ctn_uid_bits(logic [tlul_pkg::RsvdWidth-1:0] rsvd);
    // Waive unused bits
    logic unused_rsvd_bits;
    unused_rsvd_bits = ^{rsvd};

    return ctn_uid_t'(rsvd[7:0]);
  endfunction

% for racl_group, policies in racl_config['policies'].items():
<% prefix = "" if len(racl_config['policies'].keys()) == 1 else f"{racl_group.upper()}_" %>\
  /**
   * Policies for group ${racl_group}
   */

  % for policy in policies:
  /*
   * Policy ${policy['name']} allowed READ roles:
   *   ${', '.join(policy['allowed_wr'])}
   */
  parameter racl_policy_t RACL_POLICY_${prefix}${policy['name'].upper()}_RD_DEFAULT = 16'h${f"{policy['rd_default']:x}"};

  /**
   * Policy ${policy['name']} allowed WRITE roles:
   *   ${', '.join(policy['allowed_wr'])}
   */
  parameter racl_policy_t RACL_POLICY_${prefix}${policy['name'].upper()}_WR_DEFAULT = 16'h${f"{policy['wr_default']:x}"};

  % endfor
% endfor

endpackage
