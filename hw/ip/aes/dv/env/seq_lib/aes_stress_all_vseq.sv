// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs other sequences one after the other and randomly injects resets between
// sequences.

class aes_stress_all_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_stress_all_vseq)

  typedef struct {
    string name;
    bit    can_be_reset;
  } seq_desc_t;

  // The sequences that we'll run back-to-back.
  local seq_desc_t m_vseq_descs[$] = '{ '{"aes_stress_vseq",      1},
                                        '{"aes_alert_reset_vseq", 0},
                                        '{"aes_reseed_vseq",      1} };

  // Set this flag by calling require_resettable. If it is set, the stress test will only schedule
  // virtual sequences that can be reset.
  bit m_must_be_resettable = 0;

  function new (string name="");
    super.new(name);
  endfunction

  virtual function void do_copy(uvm_object rhs);
    aes_stress_all_vseq vseq_rhs;
    super.do_copy(rhs);
    if (!$cast(vseq_rhs, rhs)) `uvm_fatal(get_name(), "Cannot copy from RHS of wrong type.")
    m_must_be_resettable = vseq_rhs.m_must_be_resettable;
  endfunction

  function void require_resettable();
    m_must_be_resettable = 1;
  endfunction

  // Run a single virtual sequence (called in a loop by body)
  local
  task run_one(int unsigned idx, string name);
    uvm_sequence base_seq = create_seq_by_name(name);
    aes_base_vseq vseq;

    if (!$cast(vseq, base_seq)) begin
      `uvm_fatal(get_name(), "Cannot downcast sequence to a dv_base_vseq.")
    end

    vseq.do_apply_reset = (do_apply_reset && !m_must_be_resettable) ? $urandom_range(0, 1) : 0;
    vseq.set_sequencer(p_sequencer);

    `uvm_info(get_name(),
              $sformatf("iteration[%0d]: starting %0s, resetting %0d",
                        idx, name, vseq.do_apply_reset),
              UVM_LOW)

    vseq.start(p_sequencer);

    `uvm_info(get_name(),
              $sformatf("iteration[%0d]: ending %0s", idx, name),
              UVM_LOW)
  endtask

  task body();
    `uvm_info(`gfn, $sformatf("Running %0d sub-sequences", num_trans), UVM_LOW)
    for (int i = 0; i < num_trans; i++) begin
      int unsigned idx;
      if (!std::randomize(idx) with {
            idx < m_vseq_descs.size();
            m_must_be_resettable -> m_vseq_descs[idx].can_be_reset;
          }) begin
        `uvm_fatal(get_name(), "Failed to choose virtual sequence.")
      end
      run_one(i, m_vseq_descs[idx].name);

      if (cfg.under_reset) return;
    end
  endtask

endclass
