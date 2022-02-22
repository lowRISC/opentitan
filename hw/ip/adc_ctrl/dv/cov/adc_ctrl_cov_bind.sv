// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds ADC_CTRL functional coverage interaface to the top level LC_CTRL module.
module adc_ctrl_cov_bind;
  bind adc_ctrl_fsm adc_ctrl_fsm_cov_if u_adc_ctrl_fsm_cov_if (.*);
endmodule
