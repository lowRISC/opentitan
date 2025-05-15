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

  bit [2:0] attr;          // {X,W,R} as seen in ATTR CSR
  bit [9:0] role;
  bit       access_permit; // 1 = permitted, 0 = denied
  bit       racl;          // 1 = permitted, 0 = denied


  covergroup attr_perm_cg;
    coverpoint idx
    {
        bins indx[] = {[0:NUM_RANGES-1]};
    }

    coverpoint access_type;

    // Enumerate every permission combo (8 bins)
    coverpoint attr
    {
        bins none = {3'b000};
        bins r    = {3'b001};
        bins w    = {3'b010};
        bins x    = {3'b100};
        bins rw   = {3'b011};
        bins rx   = {3'b101};
        bins wx   = {3'b110};
        bins rwx  = {3'b111};
    }

    coverpoint access_permit { bins deny = {0}; bins permit = {1}; }

    idx_X_access_type_X_attr_X_access_permit: cross idx, access_type, attr, access_permit
    {
        ignore_bins IG0 =    binsof (access_type) intersect {EXECUTE}
                          && binsof (attr) intersect {3'b111, 3'b110, 3'b101, 3'b100}
                          && binsof (access_permit) intersect {0};

        ignore_bins IG1 =    binsof (access_type) intersect {EXECUTE}
                          && binsof (attr) intersect {3'b000, 3'b011, 3'b001, 3'b010}
                          && binsof (access_permit) intersect {1};


        ignore_bins IG3 =    binsof (access_type) intersect {WRITE}
                          && binsof (attr) intersect {3'b111, 3'b110, 3'b011, 3'b010}
                          && binsof (access_permit) intersect {0};

        ignore_bins IG4 =    binsof (access_type) intersect {WRITE}
                          && binsof (attr) intersect {3'b000, 3'b101, 3'b001, 3'b100}
                          && binsof (access_permit) intersect {1};


        ignore_bins IG5 =    binsof (access_type) intersect {READ}
                          && binsof (attr) intersect {3'b111, 3'b101, 3'b011, 3'b001}
                          && binsof (access_permit) intersect {0};

        ignore_bins IG6 =    binsof (access_type) intersect {READ}
                          && binsof (attr) intersect {3'b000, 3'b110, 3'b010, 3'b100}
                          && binsof (access_permit) intersect {1};
    }
  endgroup


  // RACL cover group is only sampled if Range check has granted access
  // RACL checks are not performed if normal range check has failed
  covergroup racl_cg;
    coverpoint idx
    {
        bins indx[] = {[0:NUM_RANGES-1]};
    }

    coverpoint access_type;
    coverpoint role { bins ROLE[]  = {[0:15]}; bins others = default;}
    coverpoint racl { bins deny = {0}; bins permit = {1}; }

    idx_X_access_type_X_role_X_racl : cross idx, access_type,role, racl;
  endgroup

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void sample_attr_cg(int idx_i, acc_t access_type_i,
                                      bit [2:0] attr_i, bit acc_permit_i);
  extern function void sample_racl_cg(int idx_i, acc_t access_type_i,
                                      bit [2:0] role_i, bit racl_i);

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
    this.attr          = attr_i  ;
    this.access_permit = acc_permit_i;

    // sample the cg one all parameters are set
    attr_perm_cg.sample() ;
endfunction

function void ac_range_check_env_cov::sample_racl_cg(int idx_i, acc_t access_type_i,
                                                     bit [2:0] role_i, bit racl_i);
    this.idx           = idx_i;
    this.access_type   = access_type_i;
    this.role          = role_i;
    this.racl          = racl_i;

    // sample the cg one all parameters are set
    racl_cg.sample() ;
endfunction
