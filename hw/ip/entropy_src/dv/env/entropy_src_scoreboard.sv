// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_scoreboard extends cip_base_scoreboard #(
    .CFG_T(entropy_src_env_cfg),
    .RAL_T(entropy_src_reg_block),
    .COV_T(entropy_src_env_cov)
  );
  `uvm_component_utils(entropy_src_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)))  csrng_fifo;
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH)))  rng_fifo;

  // local queues to hold incoming packets pending comparison
  push_pull_item#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))  csrng_q[$];
  push_pull_item#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))  rng_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
    join_none
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    // TODO Turned off do_read_check for polling, add prediction
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
         do_read_check = 1'b0;
      end
      "intr_enable": begin
      end
      "intr_test": begin
      end
      "regen": begin
      end
      "conf": begin
      end
      "rev": begin
      end
      "rate": begin
      end
      "entropy_control": begin
      end
       "entropy_data": begin
         do_read_check = 1'b0;
      end
      "health_test_windows": begin
      end
      "repcnt_thresholds": begin
      end
      "adaptp_hi_thresholds": begin
      end
      "adaptp_lo_thresholds": begin
      end
      "bucket_thresholds": begin
      end
      "markov_thresholds": begin
      end
      "repcnt_hi_watermarks": begin
      end
      "adaptp_hi_watermarks": begin
      end
      "adaptp_lo_watermarks": begin
      end
      "bucket_hi_watermarks": begin
      end
      "markov_hi_watermarks": begin
      end
      "repcnt_total_fails": begin
      end
      "adaptp_hi_total_fails": begin
      end
      "adaptp_lo_total_fails": begin
      end
      "bucket_total_fails": begin
      end
      "markov_total_fails": begin
      end
      "alert_threshold": begin
      end
      "alert_fail_counts": begin
      end
      "debug_status": begin
      end
      "seed": begin
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
