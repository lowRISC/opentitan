// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Shorthand to create and send a TL error seq
// Set low priority (1) to send error item to TL agent, so when crossing error item with normal
// seq, normal seq with default priority (100) has the priority to access TL driver
`define create_tl_access_error_case(task_name_, with_c_, seq_t_ = tl_host_custom_seq) \
  begin \
    seq_t_ tl_seq; \
    `uvm_info(`gfn, {"Running ", `"task_name_`"}, UVM_HIGH) \
    `uvm_create_on(tl_seq, p_sequencer.tl_sequencer_h) \
    if (cfg.zero_delays) begin \
      tl_seq.min_req_delay = 0; \
      tl_seq.max_req_delay = 0; \
    end \
    tl_seq.req_abort_pct = $urandom_range(0, 100); \
    `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq, with_c_) \
    csr_utils_pkg::increment_outstanding_access(); \
    `uvm_send_pri(tl_seq, 1) \
    csr_utils_pkg::decrement_outstanding_access(); \
  end

virtual task tl_access_unmapped_addr();
  bit [BUS_AW-1:0] normalized_csr_addrs[] = new[cfg.csr_addrs.size()];
  bit [BUS_AW-1:0] csr_base_addr = cfg.ral.default_map.get_base_addr();

  // calculate normalized address outside the loop to improve perf
  foreach (cfg.csr_addrs[i]) normalized_csr_addrs[i] = cfg.csr_addrs[i] - csr_base_addr;
  // randomize unmapped_addr first to improve perf
  repeat ($urandom_range(10, 100)) begin
    bit [BUS_AW-1:0] unmapped_addr;

    if (cfg.under_reset) return;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(unmapped_addr,
        !((unmapped_addr & csr_addr_mask) inside {normalized_csr_addrs});
        foreach (updated_mem_ranges[i]) {
          !((unmapped_addr & csr_addr_mask)
              inside {[updated_mem_ranges[i].start_addr : updated_mem_ranges[i].end_addr]});}
        )
    `create_tl_access_error_case(
        tl_access_unmapped_addr,
        addr == unmapped_addr;)
  end
endtask

virtual task tl_write_csr_word_unaligned_addr();
  repeat ($urandom_range(10, 100)) begin
    if (cfg.under_reset) return;
    `create_tl_access_error_case(
        tl_write_csr_word_unaligned_addr,
        opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
        foreach (updated_mem_ranges[i]) {
          !((addr & csr_addr_mask)
              inside {[updated_mem_ranges[i].start_addr : updated_mem_ranges[i].end_addr]});
        }
        addr[1:0] != 2'b00;)
  end
endtask

virtual task tl_write_less_than_csr_width();
  uvm_reg all_csrs[$];

  ral.get_registers(all_csrs);
  all_csrs.shuffle();
  foreach (all_csrs[i]) begin
    dv_base_reg      csr;
    uint             msb_pos;
    bit [BUS_AW-1:0] addr;

    if (cfg.under_reset) return;
    `DV_CHECK_FATAL($cast(csr, all_csrs[i]))
    msb_pos = csr.get_msb_pos();
    addr    = csr.get_address();
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
        })
  end
endtask

virtual task tl_protocol_err();
  repeat ($urandom_range(10, 100)) begin
    if (cfg.under_reset) return;
    `create_tl_access_error_case(
        tl_protocol_err, , tl_host_protocol_err_seq
        )
  end
endtask

virtual task tl_write_mem_less_than_word();
  uint mem_idx;
  dv_base_mem mem;
  repeat ($urandom_range(10, 100)) begin
    if (cfg.under_reset) return;
    // if more than one memories, randomly select one memory
    mem_idx = $urandom_range(0, cfg.mem_ranges.size - 1);
    // only test when mem doesn't support partial write
    `downcast(mem, get_mem_by_addr(ral, cfg.mem_ranges[mem_idx].start_addr))
    if (mem.get_mem_partial_write_support()) continue;

    `create_tl_access_error_case(
        tl_write_mem_less_than_word,
        opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
        addr[1:0] == 0; // word aligned
        (addr & csr_addr_mask) inside
            {[updated_mem_ranges[mem_idx].start_addr : updated_mem_ranges[mem_idx].end_addr]};
        mask != '1 || size < 2;
        )
  end
endtask

virtual task tl_read_mem_err();
  uint mem_idx;
  repeat ($urandom_range(10, 100)) begin
    if (cfg.under_reset) return;
    // if more than one memories, randomly select one memory
    mem_idx = $urandom_range(0, cfg.mem_ranges.size - 1);
    if (get_mem_access_by_addr(ral, cfg.mem_ranges[mem_idx].start_addr) != "WO") continue;
    `create_tl_access_error_case(
        tl_read_mem_err,
        opcode == tlul_pkg::Get;
        (addr & csr_addr_mask) inside
            {[updated_mem_ranges[mem_idx].start_addr : updated_mem_ranges[mem_idx].end_addr]};
        )
  end
endtask

// generic task to check interrupt test reg functionality
virtual task run_tl_errors_vseq(int num_times = 1, bit do_wait_clk = 0);
  bit has_mem = (cfg.mem_ranges.size > 0);
  bit [BUS_AW-1:0] csr_base_addr = cfg.ral.default_map.get_base_addr();
  bit has_unmapped_addr;

  // get_addr_mask returns address map size - 1 and get_max_offset return the offset of high byte
  // in address map. The difference btw them is unmapped address
  csr_addr_mask = cfg.ral.get_addr_mask();
  has_unmapped_addr = csr_addr_mask > cfg.ral.get_max_offset();

  // word aligned. This is used to constrain the random address and LSB 2 bits are masked out
  csr_addr_mask[1:0] = 0;

  if (updated_mem_ranges.size == 0) begin
    foreach (cfg.mem_ranges[i]) begin
      updated_mem_ranges.push_back(addr_range_t'{cfg.mem_ranges[i].start_addr - csr_base_addr,
                                                 cfg.mem_ranges[i].end_addr - csr_base_addr});
    end
  end

  set_tl_assert_en(.enable(0));
  for (int trans = 1; trans <= num_times; trans++) begin
    `uvm_info(`gfn, $sformatf("Running run_tl_errors_vseq %0d/%0d", trans, num_times), UVM_LOW)
    // TODO: once devmode is not tied internally in design, randomly drive devmode_vif
    // if (cfg.en_devmode == 1) begin
    //  cfg.devmode_vif.drive($urandom_range(0, 1));
    // end

    // use multiple thread to create outstanding access
    fork
      begin: isolation_fork
        repeat ($urandom_range(10, 20)) begin
          fork
            begin
              randcase
                1: tl_write_csr_word_unaligned_addr();
                1: tl_write_less_than_csr_width();
                1: tl_protocol_err();
                // only run when unmapped addr exists
                has_unmapped_addr: tl_access_unmapped_addr();
                // only run this task when there is an mem
                has_mem: tl_write_mem_less_than_word();
                has_mem: tl_read_mem_err();
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
  end // for
  set_tl_assert_en(.enable(1));
endtask : run_tl_errors_vseq

`undef create_tl_access_error_case
