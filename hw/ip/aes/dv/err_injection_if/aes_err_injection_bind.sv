// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
module aes_err_injection_bind;

  // fault injection IF for state of main control FSM - see aes_fi_vseq.sv
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

  // fault injection IF for state of cipher core FSM - see aes_fi_vseq.sv
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

  // fault injection IF for state of CTR mode FSM - see aes_fi_vseq.sv
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

  // fault injection IF for main control FSM signals - see aes_control_fi_vseq.sv
  bind aes_control_fsm fi_control_fsm_wrapper
    #(.IfName("aes_control_fi_vif")
     )
  u_fi_ctrl_fsm (.*);

  // fault injection IF for cipher core FSM signals - see aes_cipher_fi_vseq.sv
  bind aes_cipher_control_fsm fi_cipher_fsm_wrapper
    #(.IfName("aes_cipher_control_fi_vif")
      )
  u_control_cipher_fi (.*);

  // fault injection IF for CTR mode FSM signals - see aes_ctr_fi_vseq.sv
  bind aes_ctr_fsm fi_ctr_fsm_wrapper
    #(.IfName("aes_ctr_fsm_fi_vif")
      )
  u_control_ctr_fsm_fi (.*);

  // fault injection IF for core signals - see aes_core_fi_vseq.sv
  bind aes_core fi_core_wrapper
    #(.IfName("aes_core_fi_vif")
      )
  u_core_fi
    (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .aes_ctrl_cs(u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.u_aes_control_fsm.
                   aes_ctrl_cs)
    );

endmodule
