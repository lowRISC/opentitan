// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class ac_range_check_env_cov extends cip_base_env_cov #(.CFG_T(ac_range_check_env_cfg));

  `uvm_component_utils(ac_range_check_env_cov)

  // The base class provides the following handles for use:
  // ac_range_check_env_cfg: cfg

  // Holds the type of TLUL transaction being processed by the predictor
  ac_range_check_env_pkg::access_type_e access_type_cp;

  int  idx_cp;     // Range Index for which coverage is sampled
  bit  read_cp;    // Read permission from CSR Attr field    1 = enabled, 0 = disabled
  bit  write_cp;   // Write permission from CSR Attr field   1 = enabled, 0 = disabled
  bit  execute_cp; // Execute permission from CSR Attr field 1 = enabled, 0 = disabled
  int  role_cp;    // Holds RACL Role Identifier

  bit  access_permit_cp; // Access due to permissions 1 = Access permitted, 0 = Access denied
  bit  racl_cp;          // Access due to RACL Check  1 = Access permitted, 0 = Access denied
  bit  range_en_cp;      // State of specific Range Index at sampling point
                         // 1 = enabled, 0 = disabled

  bit  addr_hit_cp;       // State of Address Check at sampling 1 = hit, 0 = miss
  bit  all_index_miss_cp; // 1 = addr miss on all indexes, 0 = addr hit on some index range

  // Primary covergroup that verifies the operation of AC_RANGE_CHECK module.
  // There are 4 parts to the cross in this covergroup.
  // - Index that had the address match
  // - Type of transaction observed
  // - RWX permissions that was configured
  // - Access Granted / Denied
  //
  // Illegal bins are specified to ensure all combinations that can never be seen are excluded from
  // coverage reports and make them clean. If ever a situation is observed where an illegal_bins is
  // sampled, it is treated on par with assertions and will trigger a simulation failure at the
  // point of sampling an illegal bin.

  covergroup attr_perm_cg;
    coverpoint idx_cp
    {
      bins index[] = {[0:NUM_RANGES-1]};
    }

    coverpoint access_type_cp;
    coverpoint read_cp    { bins disabled = {0}; bins enabled = {1}; }
    coverpoint write_cp   { bins disabled = {0}; bins enabled = {1}; }
    coverpoint execute_cp { bins disabled = {0}; bins enabled = {1}; }


    coverpoint access_permit_cp { bins deny = {0}; bins permit = {1}; }

    idx_X_access_type_X_read_X_write_X_execute_X_access_permit:
         cross idx_cp, access_type_cp, read_cp, write_cp, execute_cp, access_permit_cp
    {

      // If an execute transaction is observed and execute permission is enabled
      // the transaction can never be filtered out.
      illegal_bins deny_when_ex_is_set =
                              binsof (access_type_cp) intersect {ac_range_check_env_pkg::Execute}
                           && binsof (execute_cp) intersect {1}
                           && binsof (access_permit_cp) intersect {0};

      // If an execute transaction is observed and execute permission is disabled
      // the transaction will always be filtered out.
      illegal_bins  permit_when_ex_unset =
                              binsof (access_type_cp) intersect {ac_range_check_env_pkg::Execute}
                           && binsof (execute_cp) intersect {0}
                           && binsof (access_permit_cp) intersect {1};


      // If a write transaction is observed and write permissions are enabled
      // the transaction can never be filtered out.
      illegal_bins deny_when_wr_is_set =
                                binsof (access_type_cp) intersect {ac_range_check_env_pkg::Write}
                             && binsof (write_cp) intersect {1}
                             && binsof (access_permit_cp) intersect {0};

      // If a write transaction is observed and write permission is disabled
      // the transaction will always be filtered out.
      illegal_bins permit_when_wr_unset =
                                binsof (access_type_cp) intersect {ac_range_check_env_pkg::Write}
                             && binsof (write_cp) intersect {0}
                             && binsof (access_permit_cp) intersect {1};


      // If a read transaction is observed and read permissions are enabled
      // the transaction can never be filtered out.
      illegal_bins deny_when_rd_is_set =
                                 binsof (access_type_cp) intersect {ac_range_check_env_pkg::Read}
                              && binsof (read_cp) intersect {1}
                              && binsof (access_permit_cp) intersect {0};

      // If a read transaction is observed and read permission is disabled
      // the transaction will always be filtered out.
      illegal_bins permit_when_rd_unset =
                                 binsof (access_type_cp) intersect {ac_range_check_env_pkg::Read}
                              && binsof (read_cp) intersect {0}
                              && binsof (access_permit_cp) intersect {1};
    }
  endgroup : attr_perm_cg


  // RACL checks are not performed when normal range check has failed.
  // This covergroup is sampled when RACL checks are performed.
  covergroup racl_cg;
    coverpoint idx_cp
    {
      bins index[] = {[0:NUM_RANGES-1]};
    }

    coverpoint role_cp
    {
      bins role[]  = {[0:NUM_ROLES-1]};
    }

    coverpoint access_type_cp;
    coverpoint racl_cp { bins deny = {0}; bins permit = {1}; }

    idx_X_access_type_X_role_X_racl : cross idx_cp, access_type_cp, role_cp, racl_cp;
  endgroup : racl_cg

  // To observe that each index is enabled or disabled.
  covergroup range_cg;
    coverpoint idx_cp
    {
      bins index[] = {[0:NUM_RANGES-1]};
    }

    coverpoint range_en_cp { bins disabled = {0}; bins enabled = {1}; }

    idx_X_range_en : cross idx_cp, range_en_cp;
  endgroup : range_cg

  // To ensure address matches are observed on all range indexes.
  covergroup addr_match_cg;
    coverpoint idx_cp
    {
      bins index[] = {[0:NUM_RANGES-1]};
    }

    coverpoint addr_hit_cp { bins miss = {0}; bins hit = {1}; }

    idx_X_addr_hit : cross idx_cp, addr_hit_cp;
  endgroup : addr_match_cg

  // all_index_miss_cg is a negative covergroup.
  // A situtation can occur when a TLUL transaction being checked by ac_range will miss all
  // configured indexes and be denied.
  covergroup all_index_miss_cg;
    coverpoint all_index_miss_cp { bins addr_hit_seen = {0};
                                   bins addr_not_matched_in_any_index = {1}; }
  endgroup : all_index_miss_cg

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void sample_attr_cg(int idx,
                                      ac_range_check_env_pkg::access_type_e access_type,
                                      bit read_perm, bit write_perm, bit execute_perm,
                                      bit acc_permit);
  extern function void sample_racl_cg(int idx,
                                      ac_range_check_env_pkg::access_type_e access_type,
                                      int role, bit racl_check);

  extern function void sample_range_cg(int idx, bit range_en);
  extern function void sample_addr_match_cg(int idx, bit addr_hit);
  extern function void sample_all_index_miss_cg();
endclass : ac_range_check_env_cov


function ac_range_check_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
  attr_perm_cg      = new();
  racl_cg           = new();
  range_cg          = new();
  addr_match_cg     = new();
  all_index_miss_cg = new();
endfunction : new

function void ac_range_check_env_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
  // See cip_base_env_cov for details
endfunction : build_phase


function void ac_range_check_env_cov::sample_attr_cg(int idx,
                                             ac_range_check_env_pkg::access_type_e access_type,
                                             bit read_perm, bit write_perm, bit execute_perm,
                                             bit acc_permit);
  this.idx_cp           = idx;
  this.access_type_cp   = access_type;
  this.access_permit_cp = acc_permit;
  this.read_cp          = read_perm;
  this.write_cp         = write_perm;
  this.execute_cp       = execute_perm;

  attr_perm_cg.sample();
endfunction : sample_attr_cg

function void ac_range_check_env_cov::sample_racl_cg(int idx,
                                             ac_range_check_env_pkg::access_type_e access_type,
                                             int role, bit racl_check);
  this.idx_cp         = idx;
  this.access_type_cp = access_type;
  this.role_cp        = role;
  this.racl_cp        = racl_check;

  racl_cg.sample();
endfunction : sample_racl_cg

function void ac_range_check_env_cov::sample_range_cg(int idx, bit range_en);
  this.idx_cp      = idx;
  this.range_en_cp = range_en;

  range_cg.sample();
endfunction : sample_range_cg

function void ac_range_check_env_cov::sample_addr_match_cg(int idx, bit addr_hit);
  this.idx_cp      = idx;
  this.addr_hit_cp = addr_hit;

  addr_match_cg.sample();

  if (addr_hit) begin
    this.all_index_miss_cp = 0;
    all_index_miss_cg.sample();
  end
endfunction : sample_addr_match_cg

function void ac_range_check_env_cov::sample_all_index_miss_cg();
  this.all_index_miss_cp = 1;
  all_index_miss_cg.sample();
endfunction : sample_all_index_miss_cg
