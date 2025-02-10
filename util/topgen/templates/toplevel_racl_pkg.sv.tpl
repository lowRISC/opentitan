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

  typedef struct packed {
    logic [top_pkg::TL_AW-1:0] base;
    logic [top_pkg::TL_AW-1:0] mask;
    racl_policy_sel_t          policy_sel;
  } racl_range_t;

  // Default ROT Private read policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_RD = ${racl_role_vec_len}'h${f"{racl_config['rot_private_policy_rd']:x}"};

  // Default ROT Private write policy value
  parameter racl_role_vec_t RACL_POLICY_ROT_PRIVATE_WR = ${racl_role_vec_len}'h${f"{racl_config['rot_private_policy_wr']:x}"};

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

<%doc>
  Note: The RACL parameters must be generated identically across multiple files.
        Thus, this template needs to be manually synced between the following files:
        util/raclgen.py
        util/topgen/templates/toplevel_racl_pkg.sv.tpl
        hw/top_darjeeling/templates/toplevel.sv.tpl
        hw/top_earlgrey/templates/toplevel.sv.tpl
        hw/top_englishbreakfast/templates/toplevel.sv.tpl
</%doc>\
<% import raclgen.lib as raclgen %>\
<% import math %>\
% if 'racl' in topcfg:
  /**
   * RACL groups:
% for racl_group in topcfg['racl']['policies']:
<% policy_names = [policy['name'] for policy in topcfg['racl']['policies'][racl_group]] %>\
<% policy_name_len = max( (len(name) for name in policy_names) ) %>\
<% policy_idx_len = math.ceil(math.log10(max(1,len(policy_names)+1))) %>\
   *   ${racl_group}
  % for policy_idx, policy_name in enumerate(policy_names):
   *     ${f"{policy_name}".ljust(policy_name_len)} (Idx ${f"{policy_idx}".rjust(policy_idx_len)})
  % endfor
% endfor
   */

% endif
% for m in topcfg['module']:
  % if 'racl_mappings' in m:
    % for if_name in m['racl_mappings'].keys():
<% register_mapping = m['racl_mappings'][if_name]['register_mapping'] %>\
<% window_mapping = m['racl_mappings'][if_name]['window_mapping'] %>\
<% range_mapping = m['racl_mappings'][if_name]['range_mapping'] %>\
<% racl_group = m['racl_mappings'][if_name]['racl_group'] %>\
<% group_suffix = f"_{racl_group.upper()}" if racl_group and racl_group != "Null" else "" %>\
<% if_suffix = f"_{if_name.upper()}" if if_name else "" %>\
<% reg_name_len = max( (len(name) for name in register_mapping.keys()), default=0 ) %>\
<% window_name_len = max( (len(name) for name in window_mapping.keys()), default=0 ) %>\
<% policy_sel_name = f"RACL_POLICY_SEL_{m['name'].upper()}{group_suffix}{if_suffix}" %>\
  /**
   * Policy selection vector for ${m["name"]}
   *   TLUL interface name: ${if_name}
   *   RACL group: ${racl_group}
      % if len(register_mapping) > 0:
   *   Register to policy mapping:
        % for reg_name, policy_idx in register_mapping.items():
   *     ${f"{reg_name}:".ljust(reg_name_len+1)} ${policy_names[policy_idx]} (Idx ${f"{policy_idx}".rjust(policy_idx_len)})
        % endfor
      % endif
      % if len(window_mapping) > 0:
   *   Window to policy mapping:
        % for window_name, policy_idx in window_mapping.items():
   *     ${f"{window_name}:".ljust(window_name_len+1)} ${policy_names[policy_idx]} (Idx ${f"{policy_idx}".rjust(policy_idx_len)})
        % endfor
      % endif
      % if len(range_mapping) > 0:
   *   Range to policy mapping:
        % for range in range_mapping:
   *     ${f"0x{range['base']:08x}"} -- ${f"0x{(range['base']+range['size']):08x}"} \
policy: ${policy_names[range['policy']]} (Idx ${f"{range['policy']}".rjust(policy_idx_len)})
        % endfor
      % endif
   */
      % if len(register_mapping) > 0:
<% policy_sel_value = ", ".join(map(str, reversed(register_mapping.values())))%>\
<% policy_sel_value = "\n    ".join(textwrap.wrap(policy_sel_value, 94))%>\
  parameter racl_policy_sel_t ${policy_sel_name} [${len(register_mapping)}] = '{
    ${policy_sel_value}
  };
      % endif
      % for window_name, policy_idx in window_mapping.items():
  parameter racl_policy_sel_t ${policy_sel_name}_WIN_${window_name.upper()} = ${policy_idx};
      % endfor
      % if len(range_mapping) > 0:
  parameter racl_policy_sel_t ${policy_sel_name}_NUM_RANGES = ${len(range_mapping)};
<% value =  ",\\n".join(map(raclgen.format_parameter_range_value, range_mapping)) %>\
  parameter racl_range_t ${policy_sel_name}_RANGES [${len(range_mapping)}] = '{
    ${value}
  };
      % endif

    % endfor
  % endif
% endfor
endpackage
