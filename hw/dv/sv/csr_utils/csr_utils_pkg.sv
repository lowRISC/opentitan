// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csr_utils_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types and variables
  uint        outstanding_accesses        = 0;
  uint        default_timeout_ns          = 1_000_000; // 1ms
  uint        default_spinwait_timeout_ns = 10_000_000; // 10ms
  string      msg_id                      = "csr_utils";
  bit         default_csr_blocking        = 1;
  uvm_check_e default_csr_check           = UVM_CHECK;
  bit         under_reset                 = 0;
  int         max_outstanding_accesses    = 100;

  // csr field struct - hold field specific params
  typedef struct {
    uvm_reg         csr;
    uvm_reg_field   field;
    uvm_reg_data_t  mask;
    uint            shift;
  } csr_field_t;

  function automatic void increment_outstanding_access();
    outstanding_accesses++;
  endfunction

  function automatic void decrement_outstanding_access();
    outstanding_accesses--;
  endfunction

  task automatic wait_no_outstanding_access();
    wait(outstanding_accesses == 0);
  endtask

  function automatic void clear_outstanding_access();
    outstanding_accesses = 0;
  endfunction

  // timeout may happen if we issue too many non-blocking accesses at once
  // limit the nonblocking items to be up to max outstanding
  task automatic wait_if_max_outstanding_accesses_reached(int max = max_outstanding_accesses);
    wait(outstanding_accesses <= max);
  endtask

  function automatic void reset_asserted();
    under_reset = 1;
  endfunction

  function automatic void reset_deasserted();
    under_reset = 0;
  endfunction

  // Get all valid csr addrs - useful to check if incoming addr falls in the csr range.
  function automatic void get_csr_addrs(input uvm_reg_block ral, ref uvm_reg_addr_t csr_addrs[$]);
    uvm_reg csrs[$];
    ral.get_registers(csrs);
    foreach (csrs[i]) begin
      csr_addrs.push_back(csrs[i].get_address());
    end
  endfunction

  // Get all valid mem addr ranges - useful to check if incoming addr falls in the mem range.
  function automatic void get_mem_addr_ranges(uvm_reg_block ral, ref addr_range_t mem_ranges[$]);
    uvm_mem mems[$];
    ral.get_memories(mems);
    foreach (mems[i]) begin
      addr_range_t mem_range;
      mem_range.start_addr = mems[i].get_address();
      mem_range.end_addr   = mem_range.start_addr +
                             mems[i].get_size() * mems[i].get_n_bytes() - 1;
      mem_ranges.push_back(mem_range);
    end
  endfunction

  // get mem object from address
  function automatic uvm_mem get_mem_by_addr(uvm_reg_block ral, uvm_reg_addr_t addr);
    uvm_mem mem;
    addr[1:0] = 0;
    mem = ral.default_map.get_mem_by_offset(addr);
    `DV_CHECK_NE_FATAL(mem, null, $sformatf("Can't find any mem with addr 0x%0h", addr), msg_id)
    return mem;
  endfunction

  // get mem access like RW, RO
  function automatic string get_mem_access_by_addr(uvm_reg_block ral, uvm_reg_addr_t addr);
    uvm_mem mem = get_mem_by_addr(ral, addr);
    return mem.get_access();
  endfunction

  // This fucntion return mirrored value of reg/field of given RAL
  function automatic uvm_reg_data_t get_reg_fld_mirror_value(uvm_reg_block ral,
                                                             string        reg_name,
                                                             string        field_name  = "");
    uvm_reg         csr;
    uvm_reg_field   fld;
    uvm_reg_data_t  result;
    string          msg_id = {csr_utils_pkg::msg_id, "::get_reg_fld_mirror_value"};
    csr = ral.get_reg_by_name(reg_name);
    `DV_CHECK_NE_FATAL(csr, null, "", msg_id)
    // return field mirror value if field_name is passed, else return reg mirror value
    if (field_name != "") begin
      fld = csr.get_field_by_name(field_name);
      `DV_CHECK_NE_FATAL(fld, null, "", msg_id)
      result = fld.get_mirrored_value();
    end
    else begin
      result = csr.get_mirrored_value();
    end
    return result;
  endfunction : get_reg_fld_mirror_value

  // This function attempts to cast a given uvm_object ptr into uvm_reg or uvm_reg_field. If cast
  // is successful on either, then set the appropriate csr_field_t return values.
  function automatic csr_field_t decode_csr_or_field(input uvm_object ptr);
    uvm_reg       csr;
    uvm_reg_field fld;
    csr_field_t   result;
    string        msg_id = {csr_utils_pkg::msg_id, "::decode_csr_or_field"};

    if ($cast(csr, ptr)) begin
      // return csr object with null field; set the mask to all 1s and shift to 0
      result.csr = csr;
      result.mask = '1;
      result.shift = 0;
    end
    else if ($cast(fld, ptr)) begin
      // return csr field object; return the appropriate mask and shift values
      result.csr = fld.get_parent();
      result.field = fld;
      result.mask = (1 << fld.get_n_bits()) - 1;
      result.shift = fld.get_lsb_pos();
    end
    else begin
      `uvm_fatal(msg_id, $sformatf("ptr %0s is not of type uvm_reg or uvm_reg_field",
                                   ptr.get_full_name()))
    end
    return result;
  endfunction : decode_csr_or_field

  // mask and shift data to extract the value specific to that supplied field
  function automatic uvm_reg_data_t get_field_val(uvm_reg_field   field,
                                                  uvm_reg_data_t  value);
    uvm_reg_data_t  mask = (1 << field.get_n_bits()) - 1;
    uint            shift = field.get_lsb_pos();
    get_field_val = (value >> shift) & mask;
  endfunction

  // get updated reg value by using new specific field value
  function automatic uvm_reg_data_t get_csr_val_with_updated_field(uvm_reg_field   field,
                                                                   uvm_reg_data_t  csr_value,
                                                                   uvm_reg_data_t  field_value);
    uvm_reg_data_t  mask = (1 << field.get_n_bits()) - 1;
    uint            shift = field.get_lsb_pos();
    csr_value = csr_value & ~(mask << shift) | ((mask & field_value) << shift);
    return csr_value;
  endfunction

  // wait until current csr op is complete
  task automatic csr_wait(input uvm_reg csr);
    `uvm_info(msg_id, $sformatf("%0s: wait_busy: %0b",
                                csr.get_full_name(), csr.m_is_busy), UVM_HIGH)
    wait(csr.m_is_busy == 1'b0);
    `uvm_info(msg_id, $sformatf("%0s: done wait_busy: %0b",
                                csr.get_full_name(), csr.m_is_busy), UVM_HIGH)
  endtask

  task automatic csr_update(input  uvm_reg      csr,
                            input  uvm_check_e  check = default_csr_check,
                            input  uvm_path_e   path = UVM_DEFAULT_PATH,
                            input  bit          blocking = default_csr_blocking,
                            input  uint         timeout_ns = default_timeout_ns,
                            input  uvm_reg_map  map = null,
                            input  bit          en_shadow_wr = 1);
    if (blocking) begin
      csr_update_sub(csr, check, path, timeout_ns, map, en_shadow_wr);
    end else begin
      fork
        csr_update_sub(csr, check, path, timeout_ns, map, en_shadow_wr);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_update, don't use it directly
  task automatic csr_update_sub(input  uvm_reg      csr,
                                input  uvm_check_e  check = default_csr_check,
                                input  uvm_path_e   path = UVM_DEFAULT_PATH,
                                input  uint         timeout_ns = default_timeout_ns,
                                input  uvm_reg_map  map = null,
                                input  bit          en_shadow_wr = 1);
    fork
      begin : isolation_fork
        uvm_status_e  status;
        string        msg_id = {csr_utils_pkg::msg_id, "::csr_update"};

        fork
          begin
            increment_outstanding_access();
            csr_pre_write_sub(csr, en_shadow_wr);
            csr.update(.status(status), .path(path), .map(map), .prior(100));
            csr_post_write_sub(csr, en_shadow_wr);
            // when reset occurs, all items will be dropped immediately. This may end up getting
            // d_error = 1 from previous item on the bus. Skip checking it during reset
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin
            wait_timeout(timeout_ns, msg_id,
                         $sformatf("Timeout waiting to csr_update %0s (addr=0x%0h)",
                                   csr.get_full_name(), csr.get_address()));
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  task automatic csr_wr(input uvm_reg        csr,
                        input uvm_reg_data_t value,
                        input uvm_check_e    check = default_csr_check,
                        input uvm_path_e     path = UVM_DEFAULT_PATH,
                        input bit            blocking = default_csr_blocking,
                        input bit            backdoor = 0,
                        input uint           timeout_ns = default_timeout_ns,
                        input bit            predict = 0,
                        input uvm_reg_map    map = null,
                        input bit            en_shadow_wr = 1);
    if (backdoor) begin
      csr_poke(csr, value, check, predict);
    end else if (blocking) begin
      csr_wr_sub(csr, value, check, path, timeout_ns, predict, map, en_shadow_wr);
    end else begin
      fork
        begin
          csr_wr_sub(csr, value, check, path, timeout_ns, predict, map, en_shadow_wr);
        end
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_wr, don't use it directly
  task automatic csr_wr_sub(input uvm_reg        csr,
                            input uvm_reg_data_t value,
                            input uvm_check_e    check = default_csr_check,
                            input uvm_path_e     path = UVM_DEFAULT_PATH,
                            input uint           timeout_ns = default_timeout_ns,
                            input bit            predict = 0,
                            input uvm_reg_map    map = null,
                            input bit            en_shadow_wr = 1);
    fork
      begin : isolation_fork
        uvm_status_e  status;
        string        msg_id = {csr_utils_pkg::msg_id, "::csr_wr"};

        fork
          begin
            increment_outstanding_access();
            csr_pre_write_sub(csr, en_shadow_wr);
            csr.write(.status(status), .value(value), .path(path), .map(map), .prior(100));
            csr_post_write_sub(csr, en_shadow_wr);
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            // Only update the predicted value if status is ok (otherwise the write isn't completed
            // successfully and the design shouldn't have accepted the written value)
            if (status == UVM_IS_OK && predict) begin
              void'(csr.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
            end
            decrement_outstanding_access();
          end
          begin
            wait_timeout(timeout_ns, msg_id,
                         $sformatf("Timeout waiting to csr_wr %0s (addr=0x%0h)",
                                   csr.get_full_name(), csr.get_address()));
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  task automatic csr_pre_write_sub(ref uvm_reg csr, bit en_shadow_wr);
    dv_base_reg dv_reg;
    `downcast(dv_reg, csr, "", fatal, msg_id)
    if (dv_reg.get_is_shadowed()) begin
      if (en_shadow_wr) increment_outstanding_access();
      dv_reg.atomic_en_shadow_wr.get(1);
      dv_reg.set_en_shadow_wr(en_shadow_wr);
    end
  endtask

  task automatic csr_post_write_sub(ref uvm_reg csr, bit en_shadow_wr);
    dv_base_reg dv_reg;
    `downcast(dv_reg, csr, "", fatal, msg_id)
    if (dv_reg.get_is_shadowed()) begin
      // try setting en_shadow_wr back to default value 1, this function will only work if the
      // shadow reg finished both writes
      dv_reg.set_en_shadow_wr(1);
      dv_reg.atomic_en_shadow_wr.put(1);
      if (en_shadow_wr) begin
        decrement_outstanding_access();
      end
    end
  endtask

  // backdoor write csr
  task automatic csr_poke(input uvm_reg         csr,
                          input uvm_reg_data_t  value,
                          input uvm_check_e     check = default_csr_check,
                          input bit             predict = 0,
                          input bkdr_reg_path_e kind = BkdrRegPathRtl);
    uvm_status_e  status;
    string        msg_id = {csr_utils_pkg::msg_id, "::csr_poke"};
    uvm_reg_data_t old_mirrored_val = csr.get_mirrored_value();

    csr.poke(.status(status), .value(value), .kind(kind.name));
    if (check == UVM_CHECK && status != UVM_IS_OK) begin
      string str;
      uvm_hdl_path_concat paths[$];
      csr.get_full_hdl_path(paths);
      foreach (paths[0].slices[i]) str = $sformatf("%0s\n%0s", str, paths[0].slices[i].path);
      `uvm_fatal(msg_id, $sformatf("poke failed for %0s, check below paths %0s",
                                   csr.get_full_name(), str))
    end
    // poke always updates predict value, if predict == 0, revert back to old mirrored value
    if (!predict || kind == BkdrRegPathRtlShadow) begin
      void'(csr.predict(.value(old_mirrored_val), .kind(UVM_PREDICT_DIRECT)));
    end
  endtask

  task automatic csr_rd(input  uvm_object     ptr, // accept reg or field
                        output uvm_reg_data_t value,
                        input  uvm_check_e    check = default_csr_check,
                        input  uvm_path_e     path = UVM_DEFAULT_PATH,
                        input  bit            blocking = default_csr_blocking,
                        input  bit            backdoor = 0,
                        input  uint           timeout_ns = default_timeout_ns,
                        input  uvm_reg_map    map = null);
    uvm_status_e status;
    if (blocking) begin
      csr_rd_sub(.ptr(ptr), .value(value), .status(status), .check(check), .path(path),
                 .backdoor(backdoor), .timeout_ns(timeout_ns), .map(map));
    end else begin
      `DV_CHECK_EQ(backdoor, 0, "Don't enable backdoor with blocking = 0", error, msg_id)
      fork
        csr_rd_sub(.ptr(ptr), .value(value), .status(status), .check(check), .path(path),
                   .backdoor(backdoor), .timeout_ns(timeout_ns), .map(map));
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_rd, don't use it directly
  task automatic csr_rd_sub(input  uvm_object     ptr, // accept reg or field
                            output uvm_reg_data_t value,
                            output uvm_status_e   status,
                            input  bit            backdoor = 0,
                            input  uvm_check_e    check = default_csr_check,
                            input  uvm_path_e     path = UVM_DEFAULT_PATH,
                            input  uint           timeout_ns = default_timeout_ns,
                            input  uvm_reg_map    map = null);
    if (backdoor) begin
        csr_peek(ptr, value, check);
        status = UVM_IS_OK;
        return;
    end
    fork
      begin : isolation_fork
        csr_field_t   csr_or_fld;
        string        msg_id = {csr_utils_pkg::msg_id, "::csr_rd"};

        fork
          begin
            increment_outstanding_access();
            csr_or_fld = decode_csr_or_field(ptr);
            if (csr_or_fld.field != null) begin
              csr_or_fld.field.read(.status(status), .value(value), .path(path), .map(map),
                                    .prior(100));
            end else begin
              csr_or_fld.csr.read(.status(status), .value(value), .path(path), .map(map),
                                  .prior(100));
            end
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin
            wait_timeout(timeout_ns, msg_id,
                         $sformatf("Timeout waiting to csr_rd %0s (addr=0x%0h)",
                                   ptr.get_full_name(), csr_or_fld.csr.get_address()));
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  // backdoor read csr
  // uvm_reg::peek() returns a 2-state value, directly get data from hdl path
  task automatic csr_peek(input uvm_object      ptr,
                          output uvm_reg_data_t value,
                          input uvm_check_e     check = default_csr_check,
                          input bkdr_reg_path_e kind = BkdrRegPathRtl);
    string      msg_id = {csr_utils_pkg::msg_id, "::csr_peek"};
    csr_field_t csr_or_fld = decode_csr_or_field(ptr);
    uvm_reg     csr = csr_or_fld.csr;

    if (csr.has_hdl_path(kind.name)) begin
      uvm_hdl_path_concat paths[$];

      csr.get_full_hdl_path(paths, kind.name);
      foreach (paths[0].slices[i]) begin
        uvm_reg_data_t field_val;
        if (uvm_hdl_read(paths[0].slices[i].path, field_val)) begin
          if (check == UVM_CHECK) `DV_CHECK_EQ($isunknown(value), 0, "", error, msg_id)
          value |= field_val << paths[0].slices[i].offset;
        end else begin
          `uvm_fatal(msg_id, $sformatf("uvm_hdl_read failed for %0s", csr.get_full_name()))
        end
      end
    end else begin
      `uvm_fatal(msg_id, $sformatf("No backdoor defined for %0s path's %0s",
                                   csr.get_full_name(), kind.name))
    end

    // if it's field, only return field value
    if (csr_or_fld.field != null) value = get_field_val(csr_or_fld.field, value);
  endtask

  task automatic csr_rd_check(input  uvm_object     ptr,
                              input  uvm_check_e    check = default_csr_check,
                              input  uvm_path_e     path = UVM_DEFAULT_PATH,
                              input  bit            blocking = default_csr_blocking,
                              input  bit            backdoor = 0,
                              input  uint           timeout_ns = default_timeout_ns,
                              input  bit            compare = 1'b1,
                              input  bit            compare_vs_ral = 1'b0,
                              input  uvm_reg_data_t compare_mask = '1,
                              input  uvm_reg_data_t compare_value = 0,
                              input  string         err_msg = "",
                              input  uvm_reg_map    map = null);
    fork
      begin : isolation_fork
        fork
          begin
            csr_field_t     csr_or_fld;
            uvm_status_e    status;
            uvm_reg_data_t  obs;
            uvm_reg_data_t  exp;
            string          msg_id = {csr_utils_pkg::msg_id, "::csr_rd_check"};

            csr_or_fld = decode_csr_or_field(ptr);

            csr_rd_sub(.ptr(ptr), .value(obs), .status(status), .check(check), .path(path),
                       .backdoor(backdoor), .timeout_ns(timeout_ns), .map(map));

            // get mirrored value after read to make sure the read reg access is updated
            if (csr_or_fld.field != null) begin
              exp = csr_or_fld.field.get_mirrored_value();
            end else begin
              exp = csr_or_fld.csr.get_mirrored_value();
            end
            if (compare && status == UVM_IS_OK && !under_reset) begin
              obs = obs & compare_mask;
              exp = (compare_vs_ral ? exp : compare_value) & compare_mask;
              `DV_CHECK_EQ(obs, exp, {"Regname: ", ptr.get_full_name(), " ", err_msg},
                    error, msg_id)
            end
          end
        join_none
        if (blocking) wait fork;
        // Add #0 to ensure that this thread starts executing before any subsequent call
        else #0;
      end : isolation_fork
    join
  endtask

  // task to read all csrs and check against ral expected value. Mainly used after reset
  task automatic read_and_check_all_csrs(input uvm_reg_block ral);
    uvm_reg ral_csrs[$];
    ral.get_registers(ral_csrs);
    ral_csrs.shuffle();

    foreach (ral_csrs[i]) csr_rd_check(.ptr(ral_csrs[i]), .compare_vs_ral(1));
  endtask

  // Checks the csr value against predicted value by reading the whole CSR or individual CSR
  // fields.
  // This task will skip read check if the CSR field is excluded.
  task automatic do_check_csr_or_field_rd(input uvm_reg         csr,
                                          input bit             do_csr_field_rd_check = $urandom(),
                                          input bit             blocking = 0,
                                          input bit             compare = 1,
                                          input bit             compare_vs_ral = 1,
                                          input csr_excl_type_e csr_excl_type = CsrNoExcl,
                                          input csr_test_type_e csr_test_type = CsrRwTest,
                                          input csr_excl_item   csr_excl_item = null);
    uvm_reg_data_t compare_mask;

    // Check if parent block or register is excluded from read-check
    if (csr_excl_item != null && csr_excl_item.is_excl(csr, csr_excl_type, csr_test_type)) begin
      `uvm_info(msg_id, $sformatf("Skipping register %0s due to CsrExclWriteCheck exclusion",
                                  csr.get_full_name()), UVM_MEDIUM)
      return;
    end

    compare_mask = get_mask_excl_fields(csr, csr_excl_type, csr_test_type, csr_excl_item);

    if (!do_csr_field_rd_check) begin
      csr_rd_check(.ptr           (csr),
                   .blocking      (blocking),
                   .compare       (compare),
                   .compare_vs_ral(compare_vs_ral),
                   .compare_mask  (compare_mask));
    end else begin
      uvm_reg_field test_fields[$];
      csr.get_fields(test_fields);
      test_fields.shuffle();
      foreach (test_fields[i]) begin
        bit field_compare = 1;
        if (csr_excl_item != null) begin
          field_compare = !csr_excl_item.is_excl(test_fields[i], csr_excl_type, csr_test_type);
        end
        csr_rd_check(.ptr           (test_fields[i]),
                     .blocking      (blocking),
                     .compare       (field_compare && compare),
                     .compare_vs_ral(compare_vs_ral));
      end
    end
   endtask

  // poll a csr or csr field continuously until it reads the expected value.
  task automatic csr_spinwait(input uvm_object      ptr,
                              input uvm_reg_data_t  exp_data,
                              input uvm_check_e     check = default_csr_check,
                              input uvm_path_e      path = UVM_DEFAULT_PATH,
                              input uvm_reg_map     map = null,
                              input uint            spinwait_delay_ns = 0,
                              input uint            timeout_ns = default_spinwait_timeout_ns,
                              input compare_op_e    compare_op = CompareOpEq,
                              input bit             backdoor = 0,
                              input uvm_verbosity   verbosity = UVM_HIGH);
    fork
      begin : isolation_fork
        csr_field_t     csr_or_fld;
        uvm_reg_data_t  read_data;
        string          msg_id = {csr_utils_pkg::msg_id, "::csr_spinwait"};

        csr_or_fld = decode_csr_or_field(ptr);
        if (backdoor && spinwait_delay_ns == 0) spinwait_delay_ns = 1;
        fork
          while (!under_reset) begin
            if (spinwait_delay_ns) #(spinwait_delay_ns * 1ns);
            csr_rd(.ptr(ptr), .value(read_data), .check(check), .path(path),
                   .blocking(1), .map(map), .backdoor(backdoor));
            `uvm_info(msg_id, $sformatf("ptr %0s == 0x%0h",
                                        ptr.get_full_name(), read_data), verbosity)
            case (compare_op)
              CompareOpEq:     if (read_data ==  exp_data) break;
              CompareOpCaseEq: if (read_data === exp_data) break;
              CompareOpNe:     if (read_data !=  exp_data) break;
              CompareOpCaseNe: if (read_data !== exp_data) break;
              CompareOpGt:     if (read_data >   exp_data) break;
              CompareOpGe:     if (read_data >=  exp_data) break;
              CompareOpLt:     if (read_data <   exp_data) break;
              CompareOpLe:     if (read_data <=  exp_data) break;
              default: begin
                `uvm_fatal(ptr.get_full_name(), $sformatf("invalid operator:%0s", compare_op))
              end
            endcase
          end
          begin
            wait_timeout(timeout_ns, msg_id, $sformatf("timeout %0s (addr=0x%0h) == 0x%0h",
                ptr.get_full_name(), csr_or_fld.csr.get_address(), exp_data));
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  task automatic mem_rd(input  uvm_mem     ptr,
                        input  int         offset,
                        output bit[31:0]   data,
                        input  uvm_check_e check = default_csr_check,
                        input  bit         blocking = default_csr_blocking,
                        input  uint        timeout_ns = default_timeout_ns,
                        input  uvm_reg_map map = null);
    if (blocking) begin
      mem_rd_sub(ptr, offset, data, check, timeout_ns, map);
    end else begin
      fork
        mem_rd_sub(ptr, offset, data, check, timeout_ns, map);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask : mem_rd

  task automatic mem_rd_sub(input  uvm_mem     ptr,
                            input  int         offset,
                            output bit[31:0]   data,
                            input  uvm_check_e check = default_csr_check,
                            input  uint        timeout_ns = default_timeout_ns,
                            input  uvm_reg_map map = null);
    fork
      begin : isolating_fork
        uvm_status_e status;
        string       msg_id = {csr_utils_pkg::msg_id, "::mem_rd"};

        fork
          begin
            increment_outstanding_access();
            ptr.read(.status(status), .offset(offset), .value(data), .map(map), .prior(100));
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin : mem_rd_timeout
            wait_timeout(timeout_ns, msg_id,
                         $sformatf("Timeout waiting to csr_rd %0s (addr=0x%0h)",
                                   ptr.get_full_name(), offset));
          end
        join_any
        disable fork;
      end : isolating_fork
    join
  endtask : mem_rd_sub

  task automatic mem_wr(input uvm_mem     ptr,
                        input int         offset,
                        input bit[31:0]   data,
                        input bit         blocking = default_csr_blocking,
                        input uint        timeout_ns = default_timeout_ns,
                        input uvm_check_e check = default_csr_check,
                        input uvm_reg_map map = null);
    if (blocking) begin
      mem_wr_sub(ptr, offset, data, timeout_ns, check, map);
    end else begin
      fork
        mem_wr_sub(ptr, offset, data, timeout_ns, check, map);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask : mem_wr

  task automatic mem_wr_sub(input uvm_mem     ptr,
                            input int         offset,
                            input bit[31:0]   data,
                            input uint        timeout_ns = default_timeout_ns,
                            input uvm_check_e check = default_csr_check,
                            input uvm_reg_map map = null);
     fork
      begin : isolation_fork
        uvm_status_e status;
        string       msg_id = {csr_utils_pkg::msg_id, "::mem_wr"};

        fork
          begin
            increment_outstanding_access();
            ptr.write(.status(status), .offset(offset), .value(data), .map(map), .prior(100));
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin
            wait_timeout(timeout_ns, msg_id,
                         $sformatf("Timeout waiting to csr_wr %0s (addr=0x%0h)",
                                   ptr.get_full_name(), offset));
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask : mem_wr_sub

  // Fields could be excluded from writes & reads - This function zeros out the excluded fields
  function automatic uvm_reg_data_t get_mask_excl_fields(uvm_reg csr,
                                                         csr_excl_type_e csr_excl_type,
                                                         csr_test_type_e csr_test_type,
                                                         csr_excl_item m_csr_excl_item);
    uvm_reg_field flds[$];
    csr.get_fields(flds);
    get_mask_excl_fields = '1;
    if (m_csr_excl_item != null) begin
      foreach (flds[i]) begin
        if (m_csr_excl_item.is_excl(flds[i], csr_excl_type, csr_test_type)) begin
          csr_field_t fld_params = decode_csr_or_field(flds[i]);
          `uvm_info(msg_id, $sformatf("Skipping field %0s due to %0s exclusion",
                                    flds[i].get_full_name(), csr_excl_type.name()), UVM_MEDIUM)
          get_mask_excl_fields &= ~(fld_params.mask << fld_params.shift);
        end
      end
    end
  endfunction

  // sources
  `include "csr_seq_lib.sv"

endpackage
