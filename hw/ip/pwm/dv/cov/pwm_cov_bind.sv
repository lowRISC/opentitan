// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds PWM functional coverage interaface to the top level PWM module.
module pwm_cov_bind;

  bind pwm pwm_cov_if u_pwm_cov_if (.*);

endmodule
