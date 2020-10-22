// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// CSR suite of sequences that do writes and reads to csrs
// includes hw_reset, rw, bit_bash and aliasing tests for csrs, and mem_walk for uvm_mems
// TODO: when mem backdoor is implemented, add uvm_mem_access_seq for backdoor rd
// The sequences perform csr writes and reads and follow the standard csr test suite. If external
// checker is enabled, then the external entity is required to update the mirrored value on
// writes. If not enabled, the sequences themselves call predict function to update the mirrored
// value. Consequently, the read values are checked against the mirrored value and not the
// previously written value. This approach is better since it takes care of special
// register and field access policies. Also, we use csr_rd_check task instead of csr_mirror to take
// field exclusions into account.
//
// Csrs to be tested is accumulated and shuffled from the supplied reg models.
// What / how many csrs to test can be further controlled in 3 ways -
// 1. Externally add specific csrs to test_csrs queue (highest prio)
// 2. Set num_test_csrs test a randomly picked set of csrs from the supplied models
// 3. Set / pass via plusarg, num_csr_chunks / test_csr_chunk
//
// Exclusions are to be provided using the csr_excl_item item (see class for more details).
class csr_base_seq extends uvm_reg_sequence #(uvm_sequence #(uvm_reg_item));
  `uvm_object_utils(csr_base_seq)

  uvm_reg_block   models[$];
  uvm_reg         all_csrs[$];
  uvm_reg         test_csrs[$];
  csr_excl_item   m_csr_excl_item;

  // By default, assume external checker (example, scoreboard) is turned off. If that is the case,
  // then writes are followed by call to predict function to update the mirrored value. Reads are
  // then checked against the mirrored value using csr_rd_check task. If external checker is
  // enabled, then we let the external checker do the predict and compare.
  // In either case, we should be able to do completely non-blocking writes and reads.
  bit external_checker = 1'b0;

  // either use num_test_csrs or {test_csr_chunk, num_csr_chunks} to test slice of all csrs
  int num_test_csrs = 0;
  int test_csr_chunk = 1;
  int num_csr_chunks = 1;

  `uvm_object_new

  // pre_start
  virtual task pre_start();
    super.pre_start();

    // create test_csrs list only if its empty
    if (test_csrs.size() == 0) set_csr_test_range();

    // create dummy m_csr_excl_item if not supplied
    if (m_csr_excl_item == null) begin
      `uvm_info(`gtn, "m_csr_excl_item is null, creating a dummy one locally", UVM_LOW)
      m_csr_excl_item = csr_excl_item::type_id::create("m_csr_excl_item");
    end
  endtask

  // post_start
  virtual task post_start();
    super.post_start();
    wait_no_outstanding_access();
    test_csrs.delete();
  endtask

  function void set_csr_excl_item(csr_excl_item item);
    this.m_csr_excl_item = item;
  endfunction

  // extract csrs and split and prune to a specified test_csr_chunk
  virtual function void set_csr_test_range();
    int   start_idx;
    int   end_idx;
    int   chunk_size;

    // extract all csrs from the model
    // TODO: add and use function here instead that allows pre filtering csrs
    all_csrs.delete();
    foreach (models[i]) begin
      models[i].get_registers(all_csrs);
    end

    if (num_test_csrs != 0) begin
      num_csr_chunks = all_csrs.size / num_test_csrs + 1;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(test_csr_chunk,
          test_csr_chunk inside {[1:num_csr_chunks]};)
    end
    else begin
      // extract test_csr_chunk, num_csr_chunks from plusargs
      void'($value$plusargs("test_csr_chunk=%0d", test_csr_chunk));
      void'($value$plusargs("num_csr_chunks=%0d", num_csr_chunks));
    end

    if (!(test_csr_chunk inside {[1:num_csr_chunks]})) begin
      `uvm_fatal(`gtn, $sformatf({{"invalid opt +test_csr_chunk=%0d, +num_csr_chunks=%0d "},
                                  {"(1 <= test_csr_chunk <= num_csr_chunks)"}},
                                  test_csr_chunk, num_csr_chunks))
    end
    chunk_size = (num_test_csrs != 0) ? num_test_csrs : (all_csrs.size / num_csr_chunks + 1);
    start_idx = (test_csr_chunk - 1) * chunk_size;
    end_idx = test_csr_chunk * chunk_size;
    if (end_idx >= all_csrs.size())
      end_idx = all_csrs.size() - 1;

    test_csrs = all_csrs[start_idx:end_idx];
    `uvm_info(`gtn, $sformatf("testing %0d csrs [%0d - %0d] in all supplied models",
                    test_csrs.size(), start_idx, end_idx), UVM_MEDIUM)
    foreach (test_csrs[i]) begin
      `uvm_info(`gtn, $sformatf("test_csrs list: %0s, reset: 0x%0x", test_csrs[i].get_full_name(),
                                 test_csrs[i].get_mirrored_value()), UVM_HIGH)
    end
    test_csrs.shuffle();
  endfunction

endclass

//--------------------------------------------------------------------------------------------------
// Class: csr_hw_reset_seq
// Brief Description: This sequence reads all CSRs and checks it against the reset value provided
// in the RAL specification. Note that this does not sufficiently qualify as the CSR HW reset test.
// The 'full' CSR HW reset test is constructed externally by running the csr_write_seq below first,
// issuing reset and only then running this sequence.
//--------------------------------------------------------------------------------------------------
class csr_hw_reset_seq extends csr_base_seq;
  `uvm_object_utils(csr_hw_reset_seq)

  `uvm_object_new

  virtual task body();
    foreach (test_csrs[i]) begin
      uvm_reg_data_t compare_mask;

      // check if parent block or register is excluded from init check
      if (m_csr_excl_item.is_excl(test_csrs[i], CsrExclInitCheck, CsrHwResetTest)) begin
        `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclInitCheck exclusion",
                                  test_csrs[i].get_full_name()), UVM_MEDIUM)
        continue;
      end

      `uvm_info(`gtn, $sformatf("Verifying reset value of register %0s",
                                test_csrs[i].get_full_name()), UVM_MEDIUM)

      compare_mask = get_mask_excl_fields(test_csrs[i], CsrExclInitCheck, CsrHwResetTest,
                                          m_csr_excl_item);
      csr_rd_check(.ptr           (test_csrs[i]),
                   .blocking      (0),
                   .compare       (!external_checker),
                   .compare_vs_ral(1'b1),
                   .compare_mask  (compare_mask));
    end
  endtask

endclass

//--------------------------------------------------------------------------------------------------
// Class: csr_write_seq
// Brief Description: This sequence writes a random value to all CSRs. It does not perform any
// checks. It is run as the first step of the CSR HW reset test.
//--------------------------------------------------------------------------------------------------
class csr_write_seq extends csr_base_seq;
  static bit test_backdoor_path_done; // only run once
  bit en_rand_backdoor_write;
  `uvm_object_utils(csr_write_seq)

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t wdata;

    // check all hdl paths are valid
    if (!test_backdoor_path_done) begin
      uvm_reg_mem_hdl_paths_seq hdl_check_seq;
      hdl_check_seq = uvm_reg_mem_hdl_paths_seq::type_id::create("hdl_check_seq");
      foreach (models[i]) begin
        hdl_check_seq.model = models[i];
        hdl_check_seq.start(null);
      end
      test_backdoor_path_done = 1;
    end

    foreach (test_csrs[i]) begin
      dv_base_reg dv_csr;
      bit         backdoor;
      // check if parent block or register is excluded from write
      if (m_csr_excl_item.is_excl(test_csrs[i], CsrExclWrite, CsrHwResetTest)) begin
        `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclWrite exclusion",
                                  test_csrs[i].get_full_name()), UVM_MEDIUM)
        continue;
      end

      `uvm_info(`gtn, $sformatf("Writing random data to register %0s",
                                test_csrs[i].get_full_name()), UVM_MEDIUM)

      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      wdata &= get_mask_excl_fields(test_csrs[i], CsrExclWrite, CsrHwResetTest, m_csr_excl_item);

      `downcast(dv_csr, test_csrs[i])
      if (en_rand_backdoor_write && !dv_csr.get_is_ext_reg()) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(backdoor,
                                           backdoor dist {0 :/ 7, 1 :/ 3};)
      end

      csr_wr(.csr(test_csrs[i]), .value(wdata), .blocking(0), .backdoor(backdoor));
    end
  endtask

endclass


//--------------------------------------------------------------------------------------------------
// Class: csr_rw_seq
// Brief Description: This seq writes a random value to a CSR and reads it back. The read value
// is checked for correctness while adhering to its access policies. A random choice is made between
// reading back the CSR as a whole or reading fields individually, so that partial accesses are made
// into the DUT as well.
//--------------------------------------------------------------------------------------------------
class csr_rw_seq extends csr_base_seq;
  `uvm_object_utils(csr_rw_seq)

  `uvm_object_new

  virtual task body();
    foreach (test_csrs[i]) begin
      uvm_reg_data_t wdata;
      uvm_reg_data_t compare_mask;
      uvm_reg_field  test_fields[$];

      // check if parent block or register is excluded from write
      if (m_csr_excl_item.is_excl(test_csrs[i], CsrExclWrite, CsrRwTest)) begin
        `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclWrite exclusion",
                                  test_csrs[i].get_full_name()), UVM_MEDIUM)
        continue;
      end

      `uvm_info(`gtn, $sformatf("Verifying register read/write for %0s",
                                test_csrs[i].get_full_name()), UVM_MEDIUM)

      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      wdata &= get_mask_excl_fields(test_csrs[i], CsrExclWrite, CsrRwTest, m_csr_excl_item);

      // if external checker is not enabled and writes are made non-blocking, then we need to
      // pre-predict so that the mirrored value will be updated. if we dont, then csr_rd_check task
      // might pick up stale mirrored value
      // the pre-predict also needs to happen after the register is being written, to make sure the
      // register is getting the updated access information.
      csr_wr(.csr(test_csrs[i]), .value(wdata), .blocking(0), .predict(!external_checker));

      do_check_csr_or_field_rd(.csr(test_csrs[i]),
                              .blocking(0),
                              .compare(!external_checker),
                              .compare_vs_ral(1),
                              .csr_excl_type(CsrExclWriteCheck),
                              .csr_test_type(CsrRwTest),
                              .csr_excl_item(m_csr_excl_item));

      wait_if_max_outstanding_accesses_reached();
    end
  endtask

endclass

//--------------------------------------------------------------------------------------------------
// Class: csr_bit_bash_seq
// Brief Description: This sequence walks a 1 through each CSR by writing one bit at a time and
// reading the CSR back. The read value is checked for correctness while adhering to its access
// policies. This verifies that there is no aliasing within the fields / bits of a CSR.
//--------------------------------------------------------------------------------------------------
class csr_bit_bash_seq extends csr_base_seq;
  `uvm_object_utils(csr_bit_bash_seq)

  `uvm_object_new

  virtual task body();
    foreach (test_csrs[i]) begin
      // check if parent block or register is excluded from write
      if (m_csr_excl_item.is_excl(test_csrs[i], CsrExclWrite, CsrBitBashTest) ||
          m_csr_excl_item.is_excl(test_csrs[i], CsrExclWriteCheck, CsrBitBashTest)) begin
        `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclWrite/WriteCheck exclusion",
                                  test_csrs[i].get_full_name()), UVM_MEDIUM)
        continue;
      end

      `uvm_info(`gtn, $sformatf("Verifying register bit bash for %0s",
                test_csrs[i].get_full_name()), UVM_MEDIUM)

      begin
        uvm_reg_field   fields[$];
        string          mode[`UVM_REG_DATA_WIDTH];
        uvm_reg_data_t  dc_mask;  // dont write or read
        uvm_reg_data_t  cmp_mask; // read but dont compare
        int             n_bits;
        string          field_access;
        int             next_lsb;

        n_bits = test_csrs[i].get_n_bytes() * 8;

        // Let's see what kind of bits we have...
        test_csrs[i].get_fields(fields);

        next_lsb = 0;
        dc_mask  = 0;
        cmp_mask = 0;

        foreach (fields[j]) begin
          int lsb, w, dc, cmp;

          field_access = fields[j].get_access(test_csrs[i].get_default_map());
          cmp = (fields[j].get_compare() == UVM_NO_CHECK);
          lsb = fields[j].get_lsb_pos();
          w   = fields[j].get_n_bits();

          // Exclude write-only fields from compare because you are not supposed to read them
          case (field_access)
            "WO", "WOC", "WOS", "WO1", "NOACCESS", "": cmp = 1;
          endcase

          // skip fields that are wr-excluded
          if (m_csr_excl_item.is_excl(fields[j], CsrExclWrite, CsrBitBashTest)) begin
            `uvm_info(`gtn, $sformatf("Skipping field %0s due to CsrExclWrite exclusion",
                                      fields[j].get_full_name()), UVM_MEDIUM)
            dc = 1;
          end

          // ignore fields that are init or rd-excluded
          cmp = m_csr_excl_item.is_excl(fields[j], CsrExclInitCheck, CsrBitBashTest) ||
                m_csr_excl_item.is_excl(fields[j], CsrExclWriteCheck, CsrBitBashTest) ;

          // Any unused bits on the right side of the LSB?
          while (next_lsb < lsb) mode[next_lsb++] = "RO";

          repeat (w) begin
            mode[next_lsb] = field_access;
            dc_mask[next_lsb] = dc;
            cmp_mask[next_lsb] = cmp;
            next_lsb++;
          end
        end

        // Any unused bits on the left side of the MSB?
        while (next_lsb < `UVM_REG_DATA_WIDTH)
          mode[next_lsb++] = "RO";

        // Bash the kth bit
        for (int k = 0; k < n_bits; k++) begin
          // Cannot test unpredictable bit behavior
          if (dc_mask[k]) continue;
          bash_kth_bit(test_csrs[i], k, mode[k], cmp_mask);
        end
      end
    end

  endtask

  task bash_kth_bit(uvm_reg       rg,
                   int            k,
                   string         mode,
                   uvm_reg_data_t mask);

    uvm_reg_data_t val;
    string          err_msg;

    `uvm_info(`gtn, $sformatf("bashing %0s bit #%0d", mode, k), UVM_HIGH)
    repeat (2) begin
      val = rg.get();
      val[k]  = ~val[k];
      err_msg = $sformatf("Wrote %0s[%0d]: %0b", rg.get_full_name(), k, val[k]);
      csr_wr(.csr(rg), .value(val), .blocking(1), .predict(!external_checker));

      // TODO, outstanding access to same reg isn't supported in uvm_reg. Need to add another seq
      // uvm_reg waits until transaction is completed, before start another read/write in same reg
      csr_rd_check(.ptr           (rg),
                   .blocking      (0),
                   .compare       (!external_checker),
                   .compare_vs_ral(1'b1),
                   .compare_mask  (~mask),
                   .err_msg       (err_msg));
    end
  endtask: bash_kth_bit

endclass

//--------------------------------------------------------------------------------------------------
// Class: csr_aliasing_seq
// Brief Description: For each CSR, this sequence writes a random value to it and reads ALL CSRs
// back. The read value of the CSR that was written is checked for correctness while adhering to its
// access policies. The read value of all other CSRs are compared against their previous values.
// This verifies that there is no aliasing across the address bits within the valid CSR space.
//--------------------------------------------------------------------------------------------------
class csr_aliasing_seq extends csr_base_seq;
  `uvm_object_utils(csr_aliasing_seq)

  `uvm_object_new

  virtual task body();
    foreach(test_csrs[i]) begin
      uvm_reg_data_t wdata;

      // check if parent block or register is excluded
      if (m_csr_excl_item.is_excl(test_csrs[i], CsrExclWrite, CsrAliasingTest)) begin
        `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclWrite exclusion",
                                  test_csrs[i].get_full_name()), UVM_MEDIUM)
        continue;
      end

      `uvm_info(`gtn, $sformatf("Verifying register aliasing for %0s",
                                test_csrs[i].get_full_name()), UVM_MEDIUM)

      `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
      wdata &= get_mask_excl_fields(test_csrs[i], CsrExclWrite, CsrAliasingTest, m_csr_excl_item);
      csr_wr(.csr(test_csrs[i]), .value(wdata), .blocking(0), .predict(!external_checker));

      all_csrs.shuffle();
      foreach (all_csrs[j]) begin
        uvm_reg_data_t compare_mask;

        // check if parent block or register is excluded
        if (m_csr_excl_item.is_excl(all_csrs[j], CsrExclInitCheck, CsrAliasingTest) ||
            m_csr_excl_item.is_excl(all_csrs[j], CsrExclWriteCheck, CsrAliasingTest)) begin
          `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclInit/WriteCheck exclusion",
                                    all_csrs[j].get_full_name()), UVM_MEDIUM)
          continue;
        end

        compare_mask = get_mask_excl_fields(all_csrs[j], CsrExclWriteCheck, CsrAliasingTest,
                                            m_csr_excl_item);
        csr_rd_check(.ptr           (all_csrs[j]),
                     .blocking      (0),
                     .compare       (!external_checker),
                     .compare_vs_ral(1'b1),
                     .compare_mask  (compare_mask));
      end
      wait_no_outstanding_access();
    end
  endtask

endclass

//--------------------------------------------------------------------------------------------------
// Class: csr_mem_walk_seq
// Brief Description: This seq walks through each address of the memory by running the default
// UVM mem walk sequence.
//--------------------------------------------------------------------------------------------------
class csr_mem_walk_seq extends csr_base_seq;
  uvm_mem_walk_seq mem_walk_seq;

  `uvm_object_utils(csr_mem_walk_seq)

  `uvm_object_new

  virtual task body();
    mem_walk_seq = uvm_mem_walk_seq::type_id::create("mem_walk_seq");
    foreach (models[i]) begin
      mem_walk_seq.model = models[i];
      mem_walk_seq.start(null);
    end
  endtask : body

endclass
