// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_alert_cg_wrap;
  // This covergroup samples alerts triggered.
  covergroup alert_cg(string name) with function sample (bit triggered);
    option.name = name;
    option.per_instance = 1;

    // It is only interesting when the alert was actually triggered.
    triggered_cp: coverpoint triggered {
       ignore_bins ignore = {0};
    }
  endgroup

  function new(string name);
     alert_cg = new(name);
  endfunction

  function void sample(bit triggered);
    alert_cg.sample(triggered);
  endfunction
endclass

class chip_spi_device_cg_wrap;

  // This covergroup is only relevanf for those command info slots which have
  // the read pipeline available (5 <= slots <= 10): READ_NORMAL, READ_FAST,
  // READ_DUAL, READ_QUAD READ_DUALIO READ_QUADIO
  covergroup read_pipeline_cg(string name = "read_pipeline_cg")
    with function sample (bit [1:0] read_pipeline_mode);

    option.name         = name;
    option.per_instance = 1;

    read_pipeline_mode_cp: coverpoint read_pipeline_mode {
      bins zero_stages           = {0};
      bins two_stages_half_cycle = {1};
      bins two_stages_full_cycle = {2};
      ignore_bins ignore         = {3};
    }
  endgroup

  function new (string name = "chip_spi_device_cg_wrap");
    read_pipeline_cg = new("read_pipeline_cg");
  endfunction

  function void sample_read_pipeline (bit [1:0] read_pipeline_mode);
    read_pipeline_cg.sample(read_pipeline_mode);
  endfunction
endclass


class chip_env_cov extends cip_base_env_cov #(.CFG_T(chip_env_cfg));
  `uvm_component_utils(chip_env_cov)

  // the base class provides the following handles for use:
  // chip_env_cfg: cfg

  // covergroups
  chip_alert_cg_wrap alert_cg_wrap[NUM_ALERTS];
  chip_spi_device_cg_wrap spi_device_cg_wrap;

  function new(string name, uvm_component parent);
    super.new(name, parent);

    // instantiate all covergroups here
    `uvm_info(`gfn, $sformatf("Instantiating %0d alert_cg wrappers", NUM_ALERTS), UVM_MEDIUM)
    foreach (alert_cg_wrap[i]) begin
      alert_cg_wrap[i] = new(LIST_OF_ALERTS[i]);
    end

    spi_device_cg_wrap = new("spi_device_cg_wrap");
  endfunction : new

endclass
