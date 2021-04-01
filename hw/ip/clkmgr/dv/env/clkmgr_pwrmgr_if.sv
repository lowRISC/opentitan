// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// clkmgr interface to pwrmgr inputs. Uses the main clk @100MHz.

interface clkmgr_pwrmgr_if(input clk);
  bit ip_clk_en;
  bit clk_status;

  function automatic void update_clk_en(input bit value);
    ip_clk_en = value;
  endfunction

  function automatic logic get_clk_status();
    return clk_status;
  endfunction
endinterface
