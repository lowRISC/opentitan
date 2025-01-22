// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<% racl_role_vec_len = 2 ** racl_config['nr_role_bits'] %>\

package top_racl_pkg;
  // Number of RACL policies used
  parameter int unsigned NrRaclPolicies = ${racl_config['nr_policies']};

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
    racl_role_vec_t read_perm;
    racl_role_vec_t write_perm;
  } racl_policy_t;

  // RACL policy vector for distributing RACL policies from the RACL widget to the subscribing IP
  typedef racl_policy_t [NrRaclPolicies-1:0] racl_policy_vec_t;

  // Default policy vector for unconnected RACL IPs
  parameter racl_policy_vec_t RACL_POLICY_VEC_DEFAULT = '0;

  // Default ROT Private read policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_RD = ${racl_role_vec_len}'h${f"{racl_config['rot_private_policy_rd']:x}"};

  // Default ROT Private write policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_WR = ${racl_role_vec_len}'h${f"{racl_config['rot_private_policy_wr']:x}"};

  // RACL information logged in case of a denial
  typedef struct packed {
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

    return racl_role_t'(rsvd[${racl_config['role_bit_msb']}:${racl_config['role_bit_lsb']}]);
  endfunction

  // Extract CTN UID bits from the TLUL reserved user bits
  function automatic ctn_uid_t tlul_extract_ctn_uid_bits(logic [tlul_pkg::RsvdWidth-1:0] rsvd);
    // Waive unused bits
    logic unused_rsvd_bits;
    unused_rsvd_bits = ^{rsvd};

    return ctn_uid_t'(rsvd[${racl_config['ctn_uid_bit_msb']}:${racl_config['ctn_uid_bit_lsb']}]);
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
  parameter racl_role_vec_t RACL_POLICY_${prefix}${policy['name'].upper()}_RD_DEFAULT = ${racl_role_vec_len}'h${f"{policy['rd_default']:x}"};

  /**
   * Policy ${policy['name']} allowed WRITE roles:
   *   ${', '.join(policy['allowed_wr'])}
   */
  parameter racl_role_vec_t RACL_POLICY_${prefix}${policy['name'].upper()}_WR_DEFAULT = ${racl_role_vec_len}'h${f"{policy['wr_default']:x}"};

  % endfor
% endfor

% for m in topcfg['module']:
  % if 'racl_mappings' in m:
    % for if_name, mapping in m['racl_mappings'].items():
  /**
   * Policy selection vector for ${m["name"]}
   */
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
  parameter int unsigned RACL_POLICY_SEL_${m["name"].upper()}${if_suffix} [${len(mapping)}] = '{${", ".join(map(str, reversed(mapping.values())))}};
  
    % endfor
  % endif
% endfor
endpackage
