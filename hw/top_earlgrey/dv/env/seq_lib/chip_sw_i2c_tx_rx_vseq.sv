// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_i2c_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_i2c_tx_rx_vseq)

  `uvm_object_new

  int clock_period_nanos = 41;
  int i2c_clock_period_nanos = 1000;
  int rise_fall_nanos = 10;
  int rise_cycles = ((rise_fall_nanos - 1) / clock_period_nanos) + 1;
  int fall_cycles = ((rise_fall_nanos - 1) / clock_period_nanos) + 1;
  int clock_period_cycles = ((i2c_clock_period_nanos - 1) / clock_period_nanos) + 1;
  int half_period_cycles = ((i2c_clock_period_nanos/2 - 1) / clock_period_nanos) + 1;

  function print_i2c_timing_cfg(uint i2c_idx);
    string str;
    str = {str, $sformatf("\n    timing_cfg.tSetupStart       : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupStart)};
    str = {str, $sformatf("\n    timing_cfg.tHoldStart        : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldStart)};
    str = {str, $sformatf("\n    timing_cfg.tClockStart       : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockStart)};
    str = {str, $sformatf("\n    timing_cfg.tClockLow         : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockLow)};
    str = {str, $sformatf("\n    timing_cfg.tSetupBit         : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupBit)};
    str = {str, $sformatf("\n    timing_cfg.tClockPulse       : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockPulse)};
    str = {str, $sformatf("\n    timing_cfg.tHoldBit          : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldBit)};
    str = {str, $sformatf("\n    timing_cfg.tClockStop        : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tClockStop)};
    str = {str, $sformatf("\n    timing_cfg.tSetupStop        : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSetupStop)};
    str = {str, $sformatf("\n    timing_cfg.tHoldStop         : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tHoldStop)};
    str = {str, $sformatf("\n    timing_cfg.tTimeOut          : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tTimeOut)};
    str = {str, $sformatf("\n    timing_cfg.enbTimeOut        : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.enbTimeOut)};
    str = {str, $sformatf("\n    timing_cfg.tStretchHostClock : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tStretchHostClock)};
    str = {str, $sformatf("\n    timing_cfg.tSdaUnstable      : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSdaUnstable)};
    str = {str, $sformatf("\n    timing_cfg.tSdaInterference  : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSdaInterference)};
    str = {str, $sformatf("\n    timing_cfg.tSclInterference  : %d",
              cfg.m_i2c_agent_cfgs[i2c_idx].timing_cfg.tSclInterference)};
    `uvm_info(`gfn, $sformatf("%s", str), UVM_MEDIUM);
  endfunction

endclass : chip_sw_i2c_tx_rx_vseq
