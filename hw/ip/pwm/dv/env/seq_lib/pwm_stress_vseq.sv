// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// sequence to stress test with reset and extended runtime
class pwm_stress_vseq extends pwm_rand_output_vseq;
  `uvm_object_utils(pwm_stress_vseq)
  `uvm_object_new

  // constraints
  constraint num_trans_c {
    num_trans inside {[5:8]};
  }

  constraint duration_cycles_c {
    duration_cycles dist {
      (NUM_CYCLES):/8,
      (2 * NUM_CYCLES):/4,
      (4 * NUM_CYCLES):/2,
      (8 * NUM_CYCLES):/1
      };
  }

  typedef enum bit [1:0] {Perf = 2'b00, Smoke = 2'b01, RandOut = 2'b10} seq_e;

  pwm_perf_vseq perf_seq;
  pwm_smoke_vseq smoke_seq;
  pwm_rand_output_vseq rand_out_seq;

  virtual task body();
    seq_e current_seq;
    bit [1:0] run_seq;

    // ensures timeout will not trigger
    foreach (cfg.m_pwm_monitor_cfg[i]) begin
      cfg.m_pwm_monitor_cfg[i].ok_to_end_delay_ns = 8 * NUM_CYCLES;
    end

    for (int i = 0; i <= num_trans; i++) begin
      run_seq = $urandom_range(0,2);
      current_seq = run_seq;
      case (current_seq)
        Perf: begin
          `uvm_info(`gfn, $sformatf("Running pwm_perf_vseq"), UVM_HIGH)
          `uvm_do(perf_seq)
          apply_reset();
        end
        Smoke: begin
          `uvm_info(`gfn, $sformatf("Running pwm_smoke_vseq"), UVM_HIGH)
          `uvm_do(smoke_seq)
          apply_reset();
        end
        RandOut: begin
          `uvm_info(`gfn, $sformatf("Running pwm_rand_output_vseq"), UVM_HIGH)
          `uvm_do(rand_out_seq)
          apply_reset();
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("seq_e randomization failure"))
        end
      endcase
    end

  endtask : body

endclass : pwm_stress_vseq
