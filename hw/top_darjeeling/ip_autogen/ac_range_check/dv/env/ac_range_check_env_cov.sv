// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

import ac_range_check_env_pkg::access_type_e;

class ac_range_check_env_cov extends cip_base_env_cov #(.CFG_T(ac_range_check_env_cfg));

  `uvm_component_utils(ac_range_check_env_cov)

  // The base class provides the following handles for use:
  // ac_range_check_env_cfg: cfg

  // Local Variables
  access_type_e access_type_cp;

  int       idx_cp;     // Range Index for which coverage is sampled
  bit       read_cp;    // {X,W,R} as seen in ATTR CSR
  bit       write_cp;   // {X,W,R} as seen in ATTR CSR
  bit       execute_cp; // {X,W,R} as seen in ATTR CSR
  int       role_cp;    // Holds RACL Role Identifier
  bit       bypass_cp;

  bit       access_permit_cp; // 1 = permitted, 0 = denied
  bit       racl_cp;          // 1 = permitted, 0 = denied
  bit       range_en_cp;      // 1 = enabled, 0 = disabled

  bit       addr_hit_cp;       // 1 = hit, 0 = miss
  bit       all_index_miss_cp; // 1 = addr miss on all indexes, 0 = addr hit on some index range

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
        // illegal_bins are used to make the coverage reports clean.
        // If ever such a situation is observed illegal_bins is treated on par with
        // assertions and will trigger a failure

        // If an execute transaction is observed and execute permission is enabled
        // the transaction can never be filtered.
        illegal_bins deny_when_ex_is_set =
                                binsof (access_type_cp) intersect {ac_range_check_env_pkg::Execute}
                             && binsof (execute_cp) intersect {1}
                             && binsof (access_permit_cp) intersect {0};

        // If an execute transaction is observed and execute permission is disabled
        // the transaction can never be permitted
        illegal_bins  permit_when_ex_unset =
                                binsof (access_type_cp) intersect {ac_range_check_env_pkg::Execute}
                             && binsof (execute_cp) intersect {0}
                             && binsof (access_permit_cp) intersect {1};


        // If a write transaction is observed and write permissions are enabled
        // the transaction can never be filtered
        illegal_bins deny_when_wr_is_set =
                                  binsof (access_type_cp) intersect {ac_range_check_env_pkg::Write}
                               && binsof (write_cp) intersect {1}
                               && binsof (access_permit_cp) intersect {0};

        // If a write transaction is observed and write permission is disabled
        // the transaction can never be permitted
        illegal_bins permit_when_wr_unset =
                                  binsof (access_type_cp) intersect {ac_range_check_env_pkg::Write}
                               && binsof (write_cp) intersect {0}
                               && binsof (access_permit_cp) intersect {1};


        // If a read transaction is observed and read permissions are enabled
        // the transaction can never be filtered
        illegal_bins deny_when_rd_is_set =
                                   binsof (access_type_cp) intersect {ac_range_check_env_pkg::Read}
                                && binsof (read_cp) intersect {1}
                                && binsof (access_permit_cp) intersect {0};

        // If a read transaction is observed and read permission is disabled
        // the transaction can never be permitted
        illegal_bins permit_when_rd_unset =
                                   binsof (access_type_cp) intersect {ac_range_check_env_pkg::Read}
                                && binsof (read_cp) intersect {0}
                                && binsof (access_permit_cp) intersect {1};
    }
  endgroup : attr_perm_cg


  // RACL cover group is only sampled if Range check has granted access
  // RACL checks are not performed if normal range check has failed
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

  covergroup range_cg;
    coverpoint idx_cp
    {
        bins index[] = {[0:NUM_RANGES-1]};
    }

    coverpoint range_en_cp { bins disabled = {0}; bins enabled = {1}; }

    idx_X_range_en : cross idx_cp, range_en_cp;
  endgroup : range_cg


  covergroup addr_match_cg;
    coverpoint idx_cp
    {
        bins index[] = {[0:NUM_RANGES-1]};
    }

    coverpoint addr_hit_cp { bins miss = {0}; bins hit = {1}; }

    idx_X_addr_hit : cross idx_cp, addr_hit_cp;
  endgroup : addr_match_cg

  covergroup all_index_miss_cg;
    coverpoint all_index_miss_cp { bins addr_hit_seen = {0};
                                   bins addr_not_matched_in_any_index = {1}; }
  endgroup : all_index_miss_cg

  covergroup bypass_cg;
    coverpoint bypass_cp { bins disabled = {0}; bins enabled = {1}; }
  endgroup : bypass_cg

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void sample_attr_cg(int idx_i, access_type_e access_type_i,
                                      bit [2:0] attr_i, bit acc_permit_i);
  extern function void sample_racl_cg(int idx_i, access_type_e access_type_i,
                                      int role_i, bit racl_i);

  extern function void sample_range_cg(int idx_i, bit range_en_i);
  extern function void sample_addr_match_cg(int idx_i, bit addr_hit_i);
  extern function void sample_all_index_miss_cg();
  extern function void sample_bypass_cg(bit bypass_en_i);
endclass : ac_range_check_env_cov


function ac_range_check_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
  attr_perm_cg      = new();
  racl_cg           = new();
  range_cg          = new();
  addr_match_cg     = new();
  all_index_miss_cg = new();
  bypass_cg         = new();
endfunction : new

function void ac_range_check_env_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
  // See cip_base_env_cov for details
endfunction : build_phase


function void ac_range_check_env_cov::sample_attr_cg(int idx_i, access_type_e access_type_i,
                                                     bit [2:0] attr_i, bit acc_permit_i);
    this.idx_cp           = idx_i;
    this.access_type_cp   = access_type_i;
    this.access_permit_cp = acc_permit_i;
    {this.execute_cp, this.write_cp, this.read_cp} = attr_i;

    attr_perm_cg.sample();
endfunction : sample_attr_cg

function void ac_range_check_env_cov::sample_racl_cg(int idx_i, access_type_e access_type_i,
                                                     int role_i, bit racl_i);
    this.idx_cp         = idx_i;
    this.access_type_cp = access_type_i;
    this.role_cp        = role_i;
    this.racl_cp        = racl_i;

    racl_cg.sample();
endfunction : sample_racl_cg

function void ac_range_check_env_cov::sample_range_cg(int idx_i, bit range_en_i);
    this.idx_cp      = idx_i;
    this.range_en_cp = range_en_i;

    range_cg.sample();
endfunction : sample_range_cg

function void ac_range_check_env_cov::sample_addr_match_cg(int idx_i, bit addr_hit_i);
    this.idx_cp      = idx_i;
    this.addr_hit_cp = addr_hit_i;

    addr_match_cg.sample();

    if (addr_hit_i) begin
      // all_index_miss_cg is a negative covergroup
      // sampling it so as not specify an ignore bin
      this.all_index_miss_cp = 0;
      all_index_miss_cg.sample();
    end
endfunction : sample_addr_match_cg

function void ac_range_check_env_cov::sample_all_index_miss_cg();
    this.all_index_miss_cp = 1;
    all_index_miss_cg.sample();
endfunction : sample_all_index_miss_cg

function void ac_range_check_env_cov::sample_bypass_cg(bit bypass_en_i);
    this.bypass_cp = bypass_en_i;
    bypass_cg.sample();
endfunction : sample_bypass_cg
