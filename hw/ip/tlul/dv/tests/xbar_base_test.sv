// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class xbar_base_test extends dv_base_test #(.ENV_T(xbar_env), .CFG_T(xbar_env_cfg));
  `uvm_component_utils(xbar_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    max_quit_count  = 50;
    test_timeout_ns = 600_000_000; // 600ms
    super.build_phase(phase);

    if (cfg.zero_delays) begin
      cfg.min_host_req_delay   = 0;
      cfg.max_host_req_delay   = 0;
      cfg.min_host_rsp_delay   = 0;
      cfg.max_host_rsp_delay   = 0;
      cfg.min_device_req_delay = 0;
      cfg.max_device_req_delay = 0;
      cfg.min_device_rsp_delay = 0;
      cfg.max_device_rsp_delay = 0;
    end
    void'($value$plusargs("min_host_req_delay=%d",   cfg.min_host_req_delay));
    void'($value$plusargs("max_host_req_delay=%d",   cfg.max_host_req_delay));
    void'($value$plusargs("min_host_rsp_delay=%d",   cfg.min_host_rsp_delay));
    void'($value$plusargs("max_host_rsp_delay=%d",   cfg.max_host_rsp_delay));
    void'($value$plusargs("min_device_req_delay=%d", cfg.min_device_req_delay));
    void'($value$plusargs("max_device_req_delay=%d", cfg.max_device_req_delay));
    void'($value$plusargs("min_device_rsp_delay=%d", cfg.min_device_rsp_delay));
    void'($value$plusargs("max_device_rsp_delay=%d", cfg.max_device_rsp_delay));
    void'($value$plusargs("num_enabled_hosts=%d",    cfg.num_enabled_hosts));
    foreach (cfg.host_agent_cfg[i]) begin
      cfg.host_agent_cfg[i].a_valid_delay_min = cfg.min_host_req_delay;
      cfg.host_agent_cfg[i].a_valid_delay_max = cfg.max_host_req_delay;
      cfg.host_agent_cfg[i].d_ready_delay_min = cfg.min_host_rsp_delay;
      cfg.host_agent_cfg[i].d_ready_delay_max = cfg.max_host_rsp_delay;
    end
    foreach (cfg.device_agent_cfg[i]) begin
      cfg.device_agent_cfg[i].d_valid_delay_min = cfg.min_device_req_delay;
      cfg.device_agent_cfg[i].d_valid_delay_max = cfg.max_device_req_delay;
      cfg.device_agent_cfg[i].a_ready_delay_min = cfg.min_device_rsp_delay;
      cfg.device_agent_cfg[i].a_ready_delay_max = cfg.max_device_rsp_delay;
    end
  endfunction : build_phase

endclass : xbar_base_test
