// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class ac_range_check_env_cov extends cip_base_env_cov #(.CFG_T(ac_range_check_env_cfg));
  typedef enum {EXECUTE, READ, WRITE} acc_t;

  `uvm_component_utils(ac_range_check_env_cov)

  // The base class provides the following handles for use:
  // ac_range_check_env_cfg: cfg

  // Covergroups
  int       idx;
  acc_t     access_type;

  bit       read;          // {X,W,R} as seen in ATTR CSR
  bit       write;         // {X,W,R} as seen in ATTR CSR
  bit       execute;       // {X,W,R} as seen in ATTR CSR
  int       role;

  bit       access_permit; // 1 = permitted, 0 = denied
  bit       racl;          // 1 = permitted, 0 = denied


  covergroup attr_perm_cg;
    coverpoint idx
    {
        bins indx[] = {[0:NUM_RANGES-1]};
    }

    coverpoint access_type;
    coverpoint read    { bins disabled = {0}; bins enabled = {1}; }
    coverpoint write   { bins disabled = {0}; bins enabled = {1}; }
    coverpoint execute { bins disabled = {0}; bins enabled = {1}; }

    coverpoint access_permit { bins deny = {0}; bins permit = {1}; }

    idx_X_access_type_X_read_X_write_X_execute_X_access_permit:
         cross idx, access_type, read, write, execute, access_permit
    {
        // IG0 captures illegal bin when execute permissions are enabled
        // If an execute transaction is observed and execute permission is enabled
        // the transaction can never be filtered
        illegal_bins deny_when_ex_is_set =    binsof (access_type) intersect {EXECUTE}
                                           && binsof (execute) intersect {1}
                                           && binsof (access_permit) intersect {0};

        // IG1 captures illegal bin when execute permissions are disabled
        // If an execute transaction is observed and execute permission is disabled
        // the transaction can never be permitted
        illegal_bins  permit_when_ex_unset =    binsof (access_type) intersect {EXECUTE}
                                             && binsof (execute) intersect {0}
                                             && binsof (access_permit) intersect {1};


        // IG3 captures illegal bin when write permissions are enabled
        // If an write transaction is observed and write permissions are enabled
        // the transaction can never be filtered
        illegal_bins deny_when_wr_is_set =    binsof (access_type) intersect {WRITE}
                                           && binsof (write) intersect {1}
                                           && binsof (access_permit) intersect {0};

        // IG4 captures illegal bin when write permissions are disabled
        // If an write transaction is observed and write permission is disabled
        // the transaction can never be permitted
        illegal_bins permit_when_wr_unset =    binsof (access_type) intersect {WRITE}
                                            && binsof (write) intersect {0}
                                            && binsof (access_permit) intersect {1};


        // IG5 captures illegal bin when read permissions are enabled
        // If an readtransaction is observed and read permissions are enabled
        // the transaction can never be filtered
        illegal_bins deny_when_rd_is_set =    binsof (access_type) intersect {READ}
                                           && binsof (read) intersect {1}
                                           && binsof (access_permit) intersect {0};

        // IG6 captures illegal bin when read permissions are disabled
        // If an read transaction is observed and read permission is disabled
        // the transaction can never be permitted
        illegal_bins permit_when_rd_unset =    binsof (access_type) intersect {READ}
                                            && binsof (read) intersect {0}
                                            && binsof (access_permit) intersect {1};
    }

  endgroup


  // RACL cover group is only sampled if Range check has granted access
  // RACL checks are not performed if normal range check has failed
  covergroup racl_cg;
    coverpoint idx
    {
        bins INDEX[] = {[0:NUM_RANGES-1]};
    }

    coverpoint role
    {
        bins ROLE[]  = {[0:NUM_ROLES-1]};
    }

    coverpoint access_type;
    coverpoint racl { bins deny = {0}; bins permit = {1}; }

    idx_X_access_type_X_role_X_racl : cross idx, access_type,role, racl;
  endgroup

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void sample_attr_cg(int idx_i, acc_t access_type_i,
                                      bit [2:0] attr_i, bit acc_permit_i);
  extern function void sample_racl_cg(int idx_i, acc_t access_type_i,
                                      bit [9:0] role_i, bit racl_i);

endclass : ac_range_check_env_cov


function ac_range_check_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
  // [instantiate covergroups here]
  attr_perm_cg = new();
  racl_cg      = new();
endfunction : new

function void ac_range_check_env_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // TODO MVy [or instantiate covergroups here]
  // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
  // See cip_base_env_cov for details
endfunction : build_phase


function void ac_range_check_env_cov::sample_attr_cg(int idx_i, acc_t access_type_i,
                                                     bit [2:0] attr_i, bit acc_permit_i);
    this.idx           = idx_i;
    this.access_type   = access_type_i;
    this.access_permit = acc_permit_i;
    {this.execute, this.write, this.read} = attr_i;

    attr_perm_cg.sample() ;
endfunction

function void ac_range_check_env_cov::sample_racl_cg(int idx_i, acc_t access_type_i,
                                                     bit [9:0] role_i, bit racl_i);
    this.idx           = idx_i;
    this.access_type   = access_type_i;
    this.role          = role_i;
    this.racl          = racl_i;

    racl_cg.sample() ;
endfunction
