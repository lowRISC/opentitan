// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_scoreboard extends cip_base_scoreboard
  #(
    .CFG_T(entropy_src_env_cfg),
    .RAL_T(entropy_src_reg_block),
    .COV_T(entropy_src_env_cov)
  );
  import entropy_src_pkg::*;

  `uvm_component_utils(entropy_src_scoreboard)

  int entropy_data_reads = 0;

  // local variables
  push_pull_item#(.HostDataWidth(RNG_BUS_WIDTH))  rng_item;
  bit [31:0]                       entropy_data_q[$];
  bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng_q[$];

  // TLM agent fifos
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH)))
      csrng_fifo;
  uvm_tlm_analysis_fifo#(push_pull_item#(.HostDataWidth(RNG_BUS_WIDTH)))
      rng_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    rng_fifo   = new("rng_fifo", this);
    csrng_fifo = new("csrng_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        collect_entropy();
        process_csrng();
      join_none
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    // TODO: Add conditioning prediction, still TBD in design
    bit do_read_check       = 1'b1;
    bit write               = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
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
        // TODO
        do_read_check = 1'b0;
      end
      "intr_enable": begin
      end
      "intr_test": begin
      end
      "regwen": begin
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

    // On reads, if do_read_check is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        case (csr.get_name())
          "entropy_data": begin
            bit [31:0] ed_pred_data = entropy_data_q.pop_front();
            `uvm_info(`gfn, $sformatf("entropy_data_prediction: %08h\n", ed_pred_data), UVM_MEDIUM)
            `DV_CHECK_FATAL(csr.predict(.value(ed_pred_data), .kind(UVM_PREDICT_READ)))
            entropy_data_reads++;
            `uvm_info(`gfn, $sformatf("entropy_data_reads: %3d\n", entropy_data_reads), UVM_MEDIUM);
          end
        endcase

        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
    end
  endtask

  function bit [FIPS_BUS_WIDTH - 1:0] get_fips_compliance(
      bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng);
    return fips_csrng[CSRNG_BUS_WIDTH +: FIPS_BUS_WIDTH];
  endfunction

  function bit [CSRNG_BUS_WIDTH - 1:0] get_csrng_seed(bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng);
    return fips_csrng[0 +: CSRNG_BUS_WIDTH];
  endfunction

  function bit [FIPS_CSRNG_BUS_WIDTH - 1:0] predict_fips_csrng(
      bit [RNG_BUS_WIDTH - 1:0] data_q[$]);
    bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng_data;
    bit [CSRNG_BUS_WIDTH - 1:0]      csrng_data;
    bit [FIPS_BUS_WIDTH - 1:0]       fips_data;

    // TODO: Add SHA3 prediction
    if (cfg.type_bypass) begin
      fips_data = '0;
    end else begin
      // TODO: support Boot mode entropy
      // Will require some changes from #9451
      fips_data = '1;
    end

    for (int i = data_q.size() - 1; i >= 0 ; i--) begin
      // Since the queue is read from back to front
      // earlier rng bits occupy the less significant bits of csrng_data
      csrng_data = (csrng_data << 4) + data_q[i];
    end
    fips_csrng_data = {fips_data, csrng_data};

    return fips_csrng_data;
  endfunction

  task collect_entropy();
    bit [15:0]              window_size;
    bit [RNG_BUS_WIDTH - 1:0] rng_data, rng_data_q[$];
    bit                     first_call;
    int                     rng_frames_per_window;

    first_call = 1'b1;

    // TODO: Read window size from register
    if (cfg.type_bypass || first_call)
      window_size = CSRNG_BUS_WIDTH;
    else
      window_size = 2048;

    // TODO: RNG bit-select
    rng_frames_per_window = window_size/RNG_BUS_WIDTH;

    forever begin
      if (cfg.rng_bit_enable == prim_mubi_pkg::MuBi4True) begin
        for (int i = 0; i < RNG_BUS_WIDTH; i++) begin
          rng_fifo.get(rng_item);
          rng_data[i] = rng_item.h_data[cfg.rng_bit_sel];
        end
      end
      else begin
        rng_fifo.get(rng_item);
        rng_data = rng_item.h_data;
      end
      rng_data_q.push_back(rng_data);

      if (rng_data_q.size() == rng_frames_per_window) begin
        bit [FIPS_CSRNG_BUS_WIDTH - 1:0] fips_csrng;
        fips_csrng = predict_fips_csrng(rng_data_q);
        if (cfg.route_software == prim_mubi_pkg::MuBi4True) begin
          bit [CSRNG_BUS_WIDTH - 1:0] csrng_seed = get_csrng_seed(fips_csrng);
          for (int i = 0; i < CSRNG_BUS_WIDTH/TL_DW; i++) begin
            bit [TL_DW - 1:0] entropy_slice = csrng_seed[i*TL_DW +: TL_DW];
            entropy_data_q.push_back(entropy_slice);
          end
        end else if (cfg.route_software == prim_mubi_pkg::MuBi4False) begin
          fips_csrng_q.push_back(fips_csrng);
        end else begin
          // TODO: invalid MuBi value for route_software: What where does data go?
        end
        for (int i = 0; i < rng_frames_per_window; i++) begin
          rng_data_q.delete();
        end
      end
      first_call = 1'b0;
    end
  endtask

  virtual task process_csrng();
    push_pull_item#(.HostDataWidth(FIPS_CSRNG_BUS_WIDTH))  item;
    bit [FIPS_CSRNG_BUS_WIDTH - 1:0]   fips_csrng_data;

   `uvm_info(`gfn, "task \"process_csrng\" starting\n", UVM_FULL)

    forever begin
      csrng_fifo.get(item);
      fips_csrng_data = item.d_data;
      `uvm_info(`gfn, "process_csrng: new item: %096h\n", UVM_MEDIUM)
      `DV_CHECK_EQ_FATAL(fips_csrng_data, fips_csrng_q[0])
      fips_csrng_q.pop_front();
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
