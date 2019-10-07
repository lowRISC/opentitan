// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Shorthand to create and send a TL error seq
`define create_tl_access_error_case(task_name_, with_c_, seq_t_ = tl_host_custom_seq) \
  begin \
    seq_t_ tl_seq; \
    `uvm_info(`gfn, {"Running ", `"task_name_`"}, UVM_HIGH) \
    `uvm_create_on(tl_seq, p_sequencer.tl_sequencer_h) \
    if (cfg.zero_delays) begin \
      tl_seq.min_req_delay = 0; \
      tl_seq.max_req_delay = 0; \
    end \
    `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq, with_c_) \
    `uvm_send(tl_seq) \
  end

virtual task tl_access_unmapped_addr();
  repeat ($urandom_range(50, 100)) begin
    `create_tl_access_error_case(
        tl_access_unmapped_addr,
        foreach (cfg.csr_addrs[i]) {
          {addr[TL_AW-1:2], 2'b00} % cfg.csr_addr_map_size !=
              cfg.csr_addrs[i] - cfg.csr_base_addr;
        }
        foreach (cfg.mem_addrs[i]) {
          !(addr % cfg.csr_addr_map_size
              inside {[cfg.mem_addrs[i].start_addr : cfg.mem_addrs[i].end_addr]});
        })
  end
endtask

virtual task tl_write_unaligned_addr();
  repeat ($urandom_range(50, 100)) begin
    `create_tl_access_error_case(
        tl_write_unaligned_addr,
        opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
        addr[1:0] != 2'b00;)
  end
endtask

virtual task tl_write_less_than_csr_width();
  uvm_reg all_csrs[$];
  ral.get_registers(all_csrs);
  foreach (all_csrs[i]) begin
    dv_base_reg     csr;
    uint            msb_pos;
    bit [TL_AW-1:0] addr;
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

virtual task tl_write_mem_less_than_word();
  uint mem_idx;
  if (cfg.mem_addrs.size == 0) return;
  repeat ($urandom_range(50, 100)) begin
    // if more than one memories, randomly select one memory
    mem_idx = $urandom_range(0, cfg.mem_addrs.size - 1);
    `create_tl_access_error_case(
        tl_write_mem_less_than_word,
        opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData};
        addr[1:0] == 0; // word aligned
        addr inside {[cfg.mem_addrs[mem_idx].start_addr : cfg.mem_addrs[mem_idx].end_addr]};
        mask != '1 || size < 2;
        )
  end
endtask

virtual task tl_protocol_err();
  repeat ($urandom_range(50, 100)) begin
    `create_tl_access_error_case(
        tl_protocol_err, , tl_host_protocol_err_seq
        )
  end
endtask

// generic task to check interrupt test reg functionality
virtual task run_tl_errors_vseq(int num_times = 1);
  `uvm_info(`gfn, "Running run_tl_errors_vseq", UVM_LOW)
  cfg.tlul_assert_vif.disable_sva_legalAOpcode();
  cfg.tlul_assert_vif.disable_sva_sizeMatchesMask();
  cfg.tlul_assert_vif.disable_sva_addressAlignedToSize();
  cfg.tlul_assert_vif.disable_sva_maskMustBeContiguous();
  cfg.tlul_assert_vif.disable_sva_sizeGTEMask();
  cfg.tlul_assert_vif.disable_sva_d_data_known();

  for (int trans = 1; trans <= num_times * 20; trans++) begin
    if (cfg.en_devmode == 1) begin
      cfg.devmode_vif.drive($urandom_range(0, 1));
    end
    randcase
      1: tl_access_unmapped_addr();
      1: tl_write_unaligned_addr();
      1: tl_write_less_than_csr_width();
      1: tl_write_mem_less_than_word();
      1: tl_protocol_err();
    endcase
  end
  cfg.tlul_assert_vif.enable_sva_legalAOpcode();
  cfg.tlul_assert_vif.enable_sva_sizeMatchesMask();
  cfg.tlul_assert_vif.enable_sva_addressAlignedToSize();
  cfg.tlul_assert_vif.enable_sva_maskMustBeContiguous();
  cfg.tlul_assert_vif.enable_sva_sizeGTEMask();
  cfg.tlul_assert_vif.enable_sva_d_data_known();
endtask : run_tl_errors_vseq

`undef create_tl_access_error_case
