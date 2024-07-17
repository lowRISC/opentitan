// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Shorthand to create and send a TL error seq
// Set low priority (1) to send error item to TL agent, so when crossing error item with normal
// seq, normal seq with default priority (100) has the priority to access TL driver
`define create_tl_access_error_case(task_name_, with_c_,
                                    seq_t_ = tl_host_custom_seq #(cip_tl_seq_item),
                                    seqr_t)                                                \
  begin                                                                                    \
    seq_t_ tl_seq;                                                                         \
    `uvm_info(`gfn, {"Running ", `"task_name_`"}, UVM_MEDIUM)                              \
    `uvm_create_on(tl_seq, seqr_t)                                                         \
    if (cfg.zero_delays) begin                                                             \
      tl_seq.min_req_delay = 0;                                                            \
      tl_seq.max_req_delay = 0;                                                            \
    end                                                                                    \
    tl_seq.req_abort_pct = $urandom_range(0, 100);                                         \
    `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq, with_c_)                                        \
    csr_utils_pkg::increment_outstanding_access();                                         \
    `DV_SPINWAIT(`uvm_send_pri(tl_seq, 1),                                                 \
        $sformatf("Timeout: %0s with addr %0h", `"task_name_`", tl_seq.addr), 100_000_000) \
    csr_utils_pkg::decrement_outstanding_access();                                         \
  end

virtual task tl_access_unmapped_addr(string ral_name);
  addr_range_t loc_unmapped_addr_ranges[$] = updated_unmapped_addr_ranges[ral_name];

  if (loc_unmapped_addr_ranges.size() == 0) return;

  // randomize unmapped_addr first to improve perf
  repeat ($urandom_range(10, 100)) begin
    bit [BUS_AW-1:0] unmapped_addr;

    // Randomly pick which unmapped address range to target
    int idx = $urandom_range(0, loc_unmapped_addr_ranges.size()-1);

    if (cfg.stop_transaction_generators()) return;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(unmapped_addr,
        (unmapped_addr & csr_addr_mask[ral_name])
            inside {[loc_unmapped_addr_ranges[idx].start_addr :
                     loc_unmapped_addr_ranges[idx].end_addr]};
    )
    `create_tl_access_error_case(
        tl_access_unmapped_addr,
        addr == unmapped_addr;,
        ,
        p_sequencer.tl_sequencer_hs[ral_name])
  end
endtask

virtual task tl_write_less_than_csr_width(string ral_name);
  uvm_reg all_csrs[$];

  cfg.ral_models[ral_name].get_registers(all_csrs);
  all_csrs.shuffle();
  foreach (all_csrs[i]) begin
    dv_base_reg      csr;
    uint             msb_pos;
    bit [BUS_AW-1:0] addr;

    if (cfg.stop_transaction_generators()) return;
    `DV_CHECK_FATAL($cast(csr, all_csrs[i]))
    msb_pos = csr.get_msb_pos();
    addr    = csr.get_address();

    // If this is a register that might change on a write that causes an error then we shouldn't
    // generate writes to it because we might update the register contents unexpectedly.
    if (csr.writes_ignore_errors) continue;

    `create_tl_access_error_case(
        tl_write_less_than_csr_width,
        opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
        addr == local::addr;
        // constrain enabled bytes less than reg width
        if (msb_pos >= 24) {
          &mask == 0;
        } else if (msb_pos >= 16) {
          &mask[2:0] == 0;
        } else if (msb_pos >= 8) {
          &mask[1:0] == 0;
        } else { // msb_pos <= 7
          mask[0] == 0;
        },
        ,
        p_sequencer.tl_sequencer_hs[ral_name])
  end
endtask

virtual task tl_protocol_err(tl_sequencer tl_sequencer_h = p_sequencer.tl_sequencer_h);
  repeat ($urandom_range(10, 100)) begin
    if (cfg.stop_transaction_generators()) return;
    `create_tl_access_error_case(
        tl_protocol_err, , tl_host_protocol_err_seq #(cip_tl_seq_item), tl_sequencer_h
        )
  end
endtask

virtual task tl_write_mem_less_than_word(string ral_name);
  uint mem_idx;
  dv_base_mem mem;
  addr_range_t loc_mem_ranges[$] = updated_mem_ranges[ral_name];
  repeat ($urandom_range(10, 100)) begin
    if (cfg.stop_transaction_generators()) return;
    // if more than one memories, randomly select one memory
    mem_idx = $urandom_range(0, loc_mem_ranges.size - 1);
    // only test when mem doesn't support partial write
    `downcast(mem, get_mem_by_addr(cfg.ral_models[ral_name],
                                   cfg.ral_models[ral_name].mem_ranges[mem_idx].start_addr))
    if (mem.get_mem_partial_write_support()) continue;

    `create_tl_access_error_case(
        tl_write_mem_less_than_word,
        opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
        addr[1:0] == 0; // word aligned
        (addr & csr_addr_mask[ral_name]) inside
            {[loc_mem_ranges[mem_idx].start_addr : loc_mem_ranges[mem_idx].end_addr]};
        mask != '1 || size < 2;, ,
        p_sequencer.tl_sequencer_hs[ral_name]
        )
  end
endtask

virtual task tl_read_wo_mem_err(string ral_name);
  uint mem_idx;
  addr_range_t loc_mem_ranges[$] = updated_mem_ranges[ral_name];
  repeat ($urandom_range(10, 100)) begin
    if (cfg.stop_transaction_generators()) return;
    // if more than one memories, randomly select one memory
    mem_idx = $urandom_range(0, loc_mem_ranges.size - 1);
    if (get_mem_access_by_addr(cfg.ral_models[ral_name],
        cfg.ral_models[ral_name].mem_ranges[mem_idx].start_addr) != "WO") continue;
    `create_tl_access_error_case(
        tl_read_wo_mem_err,
        opcode == tlul_pkg::Get;
        (addr & csr_addr_mask[ral_name]) inside
            {[loc_mem_ranges[mem_idx].start_addr :
              loc_mem_ranges[mem_idx].end_addr]};, ,
        p_sequencer.tl_sequencer_hs[ral_name]
        )
  end
endtask

virtual task tl_write_ro_mem_err(string ral_name);
  uint mem_idx;
  addr_range_t loc_mem_ranges[$] = updated_mem_ranges[ral_name];
  repeat ($urandom_range(10, 100)) begin
    if (cfg.stop_transaction_generators()) return;
    // if more than one memories, randomly select one memory
    mem_idx = $urandom_range(0, loc_mem_ranges.size - 1);
    if (get_mem_access_by_addr(cfg.ral_models[ral_name],
        cfg.ral_models[ral_name].mem_ranges[mem_idx].start_addr) != "RO") continue;
    `create_tl_access_error_case(
        tl_write_ro_mem_err,
        opcode != tlul_pkg::Get;
        (addr & csr_addr_mask[ral_name]) inside
            {[loc_mem_ranges[mem_idx].start_addr :
              loc_mem_ranges[mem_idx].end_addr]};, ,
        p_sequencer.tl_sequencer_hs[ral_name]
        )
  end
endtask

virtual task tl_instr_type_err(string ral_name);
  repeat ($urandom_range(10, 100)) begin
    bit [BUS_AW-1:0] addr;
    bit              write;
    bit [BUS_DW-1:0] data;
    mubi4_t          instr_type;

    if (cfg.stop_transaction_generators()) return;
    `DV_CHECK_STD_RANDOMIZE_FATAL(addr);
    `DV_CHECK_STD_RANDOMIZE_FATAL(data);

    randcase
      1: begin
        // invalid instr_type
        bit[3:0] instr_type_bits;
        `DV_CHECK_STD_RANDOMIZE_FATAL(write);
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(instr_type_bits,
                                           !(instr_type_bits inside {MuBi4True, MuBi4False});)
        instr_type = mubi4_t'(instr_type_bits);
      end
      1: begin
        // write with instr_type = MuBi4True
        write = 1'b1;
        instr_type = MuBi4True;
      end
    endcase

    tl_access(.addr(addr), .write(write), .data(data), .instr_type(instr_type), .exp_err_rsp(1),
              .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
  end
endtask

virtual task run_tl_errors_vseq(int num_times = 1, bit do_wait_clk = 0);
  set_tl_assert_en(.enable(0));
  for (int trans = 1; trans <= num_times; trans++) begin
    if (cfg.stop_transaction_generators()) return;
    `uvm_info(`gfn, $sformatf("Running run_tl_errors_vseq %0d/%0d", trans, num_times), UVM_LOW)
    `loop_ral_models_to_create_threads(run_tl_errors_vseq_sub(do_wait_clk, ral_name);)
  end
  csr_utils_pkg::wait_no_outstanding_access();
  set_tl_assert_en(.enable(1));
endtask

// generic task to check interrupt test reg functionality
virtual task run_tl_errors_vseq_sub(bit do_wait_clk = 0, string ral_name);
  addr_range_t loc_mem_range[$] = cfg.ral_models[ral_name].mem_ranges;
  bit has_mem = (loc_mem_range.size > 0);
  bit [BUS_AW-1:0] csr_base_addr = cfg.ral_models[ral_name].default_map.get_base_addr();
  bit has_mem_byte_access_err;
  bit has_wo_mem;
  bit has_ro_mem;

  bit has_csr_addrs = (cfg.ral_models[ral_name].csr_addrs.size() > 0);

  // get_addr_mask returns address map size - 1 and get_max_offset return the offset of high byte
  // in address map. The difference btw them is unmapped address
  csr_addr_mask[ral_name] = cfg.ral_models[ral_name].get_addr_mask();

  // word aligned. This is used to constrain the random address and LSB 2 bits are masked out
  csr_addr_mask[ral_name][1:0] = 0;

  if (updated_mem_ranges[ral_name].size == 0) begin
    foreach (loc_mem_range[i]) begin
      updated_mem_ranges[ral_name].push_back(addr_range_t'{
          loc_mem_range[i].start_addr - csr_base_addr,
          loc_mem_range[i].end_addr - csr_base_addr});
    end
  end

  if (cfg.ral_models[ral_name].has_unmapped_addrs) begin
    addr_range_t loc_unmapped_addr_ranges[$] = cfg.ral_models[ral_name].unmapped_addr_ranges;
    foreach (loc_unmapped_addr_ranges[i]) begin
      updated_unmapped_addr_ranges[ral_name].push_back(addr_range_t'{
          loc_unmapped_addr_ranges[i].start_addr - csr_base_addr,
          loc_unmapped_addr_ranges[i].end_addr - csr_base_addr});
    end
  end

  get_all_mem_attrs(cfg.ral_models[ral_name], has_mem_byte_access_err, has_wo_mem, has_ro_mem);

  // use multiple thread to create outstanding access
  fork
    begin: isolation_fork
      repeat ($urandom_range(10, 20)) begin
        fork
          begin
            randcase
              1: tl_protocol_err(p_sequencer.tl_sequencer_hs[ral_name]);
              // only run when csr addresses exist
              has_csr_addrs: tl_write_less_than_csr_width(ral_name);

              // only run when unmapped addr exists
              cfg.ral_models[ral_name].has_unmapped_addrs: tl_access_unmapped_addr(ral_name);

              // only run this task when the error can be triggered
              has_mem_byte_access_err: tl_write_mem_less_than_word(ral_name);
              has_wo_mem: tl_read_wo_mem_err(ral_name);
              has_ro_mem: tl_write_ro_mem_err(ral_name);
              1: tl_instr_type_err(ral_name);
            endcase
          end
        join_none
      end
      wait fork;
    end: isolation_fork
  join
  // when reset occurs, end this seq ASAP to avoid killing seq while sending trans
  if (do_wait_clk) begin
    repeat($urandom_range(500, 10_000)) begin
      if (cfg.under_reset) return;
      cfg.clk_rst_vif.wait_clks(1);
    end
  end
endtask : run_tl_errors_vseq_sub

virtual task run_tl_intg_err_vseq(int num_times = 1);
  set_tl_assert_en(.enable(0));

  // If there are multiple TLUL interfaces, race condition may occurs as one TLUL is updating intg
  // status CSR while the other TLUL interface reads it. Exclude checking the CSR
  if (cfg.ral_models.size > 1) begin
    foreach (cfg.tl_intg_alert_fields[csr_field]) begin
      csr_excl_item csr_excl = get_excl_item(csr_field);
      csr_excl.add_excl(csr_field.`gfn, CsrExclCheck, CsrRwTest);
      `uvm_info(`gfn, $sformatf("Exclude CSR %s check, due to potential race condition",
                                csr_field.`gfn), UVM_MEDIUM)
    end
  end
  for (int trans = 1; trans <= num_times; trans++) begin
    if (cfg.stop_transaction_generators()) break;
    `uvm_info(`gfn, $sformatf("Running run_tl_intg_err_vseq %0d/%0d", trans, num_times),
              UVM_LOW)
    foreach (cfg.ral_models[ral_name]) begin
      run_tl_intg_err_vseq_sub(ral_name);
      dut_init("HARD");
    end
  end
  csr_utils_pkg::wait_no_outstanding_access();

  set_tl_assert_en(.enable(1));
endtask

virtual task run_tl_intg_err_vseq_sub(string ral_name);
  fork
    // run csr_rw seq to send some normal CSR accesses in parallel
    begin
      if (en_csr_vseq_w_tl_intg) begin
        `uvm_info(`gfn, "Run csr_rw seq", UVM_HIGH)
        run_csr_vseq(.csr_test_type("rw"), .ral_name(ral_name));
      end
    end
    begin
      // check integrity status before injecting fault
      foreach (cfg.tl_intg_alert_fields[csr_field]) begin
        csr_rd_check(.ptr(csr_field), .compare_vs_ral(1));
      end

      issue_tl_access_w_intg_err(ral_name);

      // Check design's response to tl_intg_error.
      // This virtual task verifies the fatal alert is firing continuously and verifies integrity
      // error status register field is set.
      check_tl_intg_error_response();
    end
  join
endtask

virtual task issue_tl_access_w_intg_err(string ral_name);
  bit [BUS_AW-1:0] addr;
  bit [BUS_DW-1:0] data = $urandom;
  bit              write = $urandom_range(0, 1);
  tl_intg_err_e    tl_intg_err_type;
  bit              has_mem = cfg.ral_models[ral_name].mem_ranges.size > 0;

  #($urandom_range(10, 1000) * 1ns);
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tl_intg_err_type,
                                     tl_intg_err_type != TlIntgErrNone;)
  randcase
    // any address
    1: addr = $urandom;
    // mem address
    has_mem: begin
      int mem_idx = $urandom_range(0, cfg.ral_models[ral_name].mem_ranges.size - 1);
      addr = $urandom_range(cfg.ral_models[ral_name].mem_ranges[mem_idx].start_addr,
                            cfg.ral_models[ral_name].mem_ranges[mem_idx].end_addr);
    end
  endcase
  tl_access(.addr(addr), .write(write), .data(data), .tl_intg_err_type(tl_intg_err_type),
            .mask(get_rand_contiguous_mask()),
            .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
endtask

virtual task check_tl_intg_error_response();
  `DV_CHECK_FATAL(cfg.tl_intg_alert_name inside {cfg.list_of_alerts}, $sformatf(
      "tl intg alert (%s) is not inside %p", cfg.tl_intg_alert_name, cfg.list_of_alerts))

  // Check both alert and CSR status update
  fork
    // This is a fatal alert and design keeps sending it until reset is issued.
    // Check alerts are triggered for a few times
    begin
      repeat ($urandom_range(5, 20)) begin
        wait_alert_trigger(cfg.tl_intg_alert_name, .wait_complete(1));
      end
    end
    begin
      // Check corresponding CSR status is updated correctly
      foreach (cfg.tl_intg_alert_fields[csr_field]) begin
        void'(csr_field.predict(.value(cfg.tl_intg_alert_fields[csr_field]),
                                .kind(UVM_PREDICT_READ)));

        csr_rd_check(.ptr(csr_field), .compare_vs_ral(1));
      end
    end
  join
endtask

virtual task run_passthru_mem_tl_intg_err_vseq(int num_times = 1);
  for (int trans = 1; trans <= num_times; trans++) begin
    if (cfg.stop_transaction_generators()) break;
    `uvm_info(`gfn, $sformatf("Running run_passthru_mem_tl_intg_err_vseq %0d/%0d",
                              trans, num_times),
              UVM_LOW)
    `loop_ral_models_to_create_threads(run_passthru_mem_tl_intg_err_vseq_sub(ral_name);)
    // no fatal alert is triggered as the intg error will be detected in ibex instead of currect
    // block.
    check_no_fatal_alerts();
    // calling dut_init to initialize the mem again
    dut_init("HARD");
  end
  csr_utils_pkg::wait_no_outstanding_access();
endtask

virtual task run_passthru_mem_tl_intg_err_vseq_sub(string ral_name);
  uvm_mem mems[$];
  dv_base_mem passthru_mems[$];

  cfg.ral_models[ral_name].get_memories(mems);

  foreach (mems[i]) begin
    dv_base_mem dv_mem;
    `downcast(dv_mem, mems[i])
    if (dv_mem.get_data_intg_passthru()) passthru_mems.push_back(dv_mem);
  end

  fork
    // run csr_rw seq to send some normal CSR accesses in parallel
    if (en_csr_vseq_w_passthru_mem_intg) begin
      `uvm_info(`gfn, "Run csr_rw seq", UVM_HIGH)
      run_csr_vseq(.csr_test_type("rw"), .ral_name(ral_name));
    end
    begin
      if (passthru_mems.size > 0) begin
        cfg.disable_d_user_data_intg_check_for_passthru_mem = 1;
        test_intg_err_in_passthru_mem(passthru_mems);
        cfg.disable_d_user_data_intg_check_for_passthru_mem = 0;
      end
    end
  join
endtask

virtual task test_intg_err_in_passthru_mem(const ref dv_base_mem mems[$]);
  foreach (mems[i]) begin
    bit [BUS_AW-1:0] offset;
    bit [BUS_AW-1:0] addr;
    bit [BUS_DW-1:0] data;
    string ral_name;
    cip_tl_seq_item tl_access_rsp;
    bit completed, saw_err;
    bit data_intg_ok;

    offset = $urandom_range(0, mems[i].get_n_bytes() - 1);
    addr = mems[i].get_address(offset);
    ral_name = mems[i].get_parent().get_name();
    // Before inject faults, this read should have correct integrity
    tl_access_sub(.addr(addr), .write(0), .data(data), .completed(completed), .saw_err(saw_err),
                  .check_rsp(1),  .rsp(tl_access_rsp),
                  .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
    `DV_CHECK_EQ(completed, 1)
    `DV_CHECK_EQ(saw_err, 0)
    void'(tl_access_rsp.is_d_chan_intg_ok(.en_rsp_intg_chk(1),
                                          .en_data_intg_chk(1),
                                          .throw_error(1)));

    `uvm_info(`gfn, $sformatf("Backdoor inject intg fault to %s addr 0x%0h", ral_name, addr),
              UVM_LOW)
    inject_intg_fault_in_passthru_mem(mems[i], addr);

    // Issue a read on the address that has been injected with integrity error
    tl_access_sub(.addr(addr), .write(0), .data(data), .completed(completed), .saw_err(saw_err),
                  .check_rsp(1),  .rsp(tl_access_rsp),
                  .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
    `DV_CHECK_EQ(completed, 1)
    `DV_CHECK_EQ(saw_err, 0)
    // data integrity should be wrong
    data_intg_ok = tl_access_rsp.is_d_chan_intg_ok(.en_rsp_intg_chk(0),
                                                   .en_data_intg_chk(1),
                                                   .throw_error(0));
    `DV_CHECK_EQ(data_intg_ok, 0)
  end
endtask

virtual function void inject_intg_fault_in_passthru_mem(dv_base_mem mem, bit [BUS_AW-1:0] addr);
  `uvm_fatal(`gfn, "This must be overridden in extended block common_vseq")
endfunction

`undef create_tl_access_error_case
