// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
module aes_err_injection_bind;

  // bind fault inject if to control_fsm
  bind aes_control_fsm signal_force
    #(.Signal("aes_ctrl_cs"),
      .IfName("aes_fi_vif"),
      .SignalWidth(aes_env_pkg::StateWidth)
     )
  u_fi
    (
     .clk          (clk_i),
     .rst_ni       (rst_ni)
    );

  // bind fault inject if to cipher fsm
  bind aes_cipher_control_fsm signal_force
    #(.Signal("aes_cipher_ctrl_cs"),
      .IfName("aes_cipher_fi_vif"),
      .SignalWidth(aes_env_pkg::StateWidth)
     )
  u_cipher_fi
    (
     .clk          (clk_i),
     .rst_ni       (rst_ni)
    );

  // bind fault inject if to round counter
  bind aes_ctr_fsm signal_force
    #(.Signal("aes_ctr_cs"),
      .IfName("aes_ctr_fi_vif"),
      .SignalWidth(aes_env_pkg::StateWidth)
     )
  u_ctr_fi
    (
     .clk          (clk_i),
     .rst_ni       (rst_ni)
    );

  bind aes_control_fsm fi_control_fsm_wrapper
    #(.IfName("aes_control_fi_vif")
     )
  u_fi_ctrl_fsm
    (
     .clk          (clk_i),
     .rst_ni       (rst_ni)
     );

  bind aes_cipher_control_fsm fi_cipher_fsm_wrapper
    #(.IfName("aes_cipher_control_fi_vif")
      )
  u_control_cipher_fi
    (
     .clk          (clk_i),
     .rst_ni       (rst_ni)
     );


endmodule
