// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csr_utils_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  export dv_base_reg_pkg::csr_field_t, dv_base_reg_pkg::decode_csr_or_field;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types and variables
  uint              outstanding_accesses        = 0;
  uint              default_timeout_ns          = 2_000_000; // 2ms
  uint              default_spinwait_timeout_ns = 10_000_000; // 10ms
  string            msg_id                      = "csr_utils";
  bit               default_csr_blocking        = 1;
  uvm_check_e       default_csr_check           = UVM_CHECK;
  bit               under_reset                 = 0;
  int               max_outstanding_accesses    = 100;
  uvm_reg_frontdoor default_user_frontdoor      = null;

  function automatic void increment_outstanding_access();
    outstanding_accesses++;
    `uvm_info("csr_utils_pkg", $sformatf("increment_outstanding_access %0d", outstanding_accesses),
              UVM_HIGH)
  endfunction

  function automatic void decrement_outstanding_access();
    outstanding_accesses--;
    `uvm_info("csr_utils_pkg", $sformatf("decrement_outstanding_access %0d", outstanding_accesses),
              UVM_HIGH)
  endfunction

  task automatic wait_no_outstanding_access();
    wait(outstanding_accesses == 0);
  endtask

  function automatic void clear_outstanding_access();
    outstanding_accesses = 0;
  endfunction

  function automatic bit has_outstanding_access();
    return outstanding_accesses > 0;
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

  // This function return mirrored value of reg/field of given RAL
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

  // Use `csr_wr` to construct `csr_update` to avoid replicated codes to handle nonblocking,
  // shadow writes etc
  task automatic csr_update(input  uvm_reg            csr,
                            input  uvm_check_e        check = default_csr_check,
                            input  uvm_path_e         path = UVM_DEFAULT_PATH,
                            input  bit                blocking = default_csr_blocking,
                            input  uint               timeout_ns = default_timeout_ns,
                            input  uvm_reg_map        map = null,
                            input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor,
                            input  bit                en_shadow_wr = 1);
    uvm_reg_field fields[$];
    uvm_reg_data_t value;

    // below is partial replication of the uvm_reg_field::update() logic in UVM1.2 source code
    if (!csr.needs_update()) return;
    csr.get_fields(fields);
    // Concatenate the write-to-update values from each field
    // Fields are stored in LSB or MSB order
    value = 0;
    foreach (fields[i]) begin
      value |= fields[i].XupdateX() << fields[i].get_lsb_pos();
    end

    csr_wr(.ptr(csr), .value(value), .check(check), .path(path), .blocking(blocking), .backdoor(0),
           .timeout_ns(timeout_ns), .predict(0), .map(map), .user_ftdr(user_ftdr),
           .en_shadow_wr(en_shadow_wr));
  endtask

  task automatic csr_wr(input uvm_object          ptr,
                        input uvm_reg_data_t      value,
                        input uvm_check_e         check = default_csr_check,
                        input uvm_path_e          path = UVM_DEFAULT_PATH,
                        input bit                 blocking = default_csr_blocking,
                        input bit                 backdoor = 0,
                        input uint                timeout_ns = default_timeout_ns,
                        input bit                 predict = 0,
                        input uvm_reg_map         map = null,
                        input uvm_reg_frontdoor   user_ftdr = default_user_frontdoor,
                        input bit                 en_shadow_wr = 1);
    if (backdoor) begin
      csr_poke(ptr, value, check, predict);
    end else begin
      csr_field_t csr_or_fld = decode_csr_or_field(ptr);

      // if it's a field write, still do full CSR write and use mirrored value for the other fields
      if (csr_or_fld.field != null) begin
        // get full CSR value
        value = get_csr_val_with_updated_field(csr_or_fld.field, `gmv(csr_or_fld.csr), value);
      end

      if (blocking) begin
        csr_wr_sub(csr_or_fld.csr, value, check, path, timeout_ns, predict, map, user_ftdr,
                   en_shadow_wr);
      end else begin
        fork
          begin
            csr_wr_sub(csr_or_fld.csr, value, check, path, timeout_ns, predict, map, user_ftdr,
                       en_shadow_wr);
          end
        join_none
        // Add #0 to ensure that this thread starts executing before any subsequent call
        #0;
      end
    end
  endtask

  // subroutine of csr_wr, don't use it directly
  task automatic csr_wr_sub(input uvm_reg             csr,
                            input uvm_reg_data_t      value,
                            input uvm_check_e         check = default_csr_check,
                            input uvm_path_e          path = UVM_DEFAULT_PATH,
                            input uint                timeout_ns = default_timeout_ns,
                            input bit                 predict = 0,
                            input uvm_reg_map         map = null,
                            input uvm_reg_frontdoor   user_ftdr = default_user_frontdoor,
                            input bit                 en_shadow_wr = 1);
    fork
      begin : isolation_fork
        string msg_id = {csr_utils_pkg::msg_id, "::csr_wr"};

        fork
          begin
            dv_base_reg dv_reg;
            `downcast(dv_reg, csr, "", fatal, msg_id)

            increment_outstanding_access();
            csr_pre_write_sub(csr, en_shadow_wr);

            csr_wr_and_predict_sub(.csr(csr), .value(value), .check(check), .path(path),
                                   .predict(predict), .map(map), .user_ftdr(user_ftdr));
            if (en_shadow_wr && dv_reg.get_is_shadowed()) begin
              csr_wr_and_predict_sub(.csr(csr), .value(value), .check(check), .path(path),
                                     .predict(predict), .map(map), .user_ftdr(user_ftdr));
            end

            csr_post_write_sub(csr, en_shadow_wr);
            decrement_outstanding_access();
          end
          begin
            `DV_WAIT_TIMEOUT(timeout_ns, msg_id,
                             $sformatf("Timeout waiting to csr_wr %0s (addr=0x%0h)",
                                       csr.get_full_name(), csr.get_address()))
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  // internal task, don't use it directly
  task automatic csr_wr_and_predict_sub(uvm_reg             csr,
                                        uvm_reg_data_t      value,
                                        uvm_check_e         check,
                                        uvm_path_e          path,
                                        bit                 predict,
                                        uvm_reg_map         map,
                                        uvm_reg_frontdoor   user_ftdr);
    uvm_status_e status;

    if (user_ftdr != null) csr.set_frontdoor(user_ftdr);
    csr.write(.status(status), .value(value), .path(path), .map(map), .prior(100));
    // TODO: need to remove the frontdoor to switch back to the default,
    // but this doesn't work: if (user_ftdr != null) ptr.set_frontdoor(null);

    if (under_reset) return;
    if (check == UVM_CHECK) begin
      `DV_CHECK_EQ(status, UVM_IS_OK,
                   $sformatf("trying to write csr %0s", csr.get_full_name()),
                   error, msg_id)
    end
    // Only update the predicted value if status is ok (otherwise the write isn't completed
    // successfully and the design shouldn't have accepted the written value)
    if (status == UVM_IS_OK && predict) begin
      void'(csr.predict(.value(value), .kind(UVM_PREDICT_WRITE)));
    end
  endtask

  task automatic csr_pre_write_sub(uvm_reg csr, bit en_shadow_wr);
    dv_base_reg dv_reg;
    `downcast(dv_reg, csr, "", fatal, msg_id)
    if (dv_reg.get_is_shadowed() && en_shadow_wr) begin
      dv_reg.atomic_en_shadow_wr.get(1);
    end
  endtask

  task automatic csr_post_write_sub(uvm_reg csr, bit en_shadow_wr);
    dv_base_reg dv_reg;
    `downcast(dv_reg, csr, "", fatal, msg_id)
    if (dv_reg.get_is_shadowed() && en_shadow_wr) begin
      dv_reg.atomic_en_shadow_wr.put(1);
    end
  endtask

  // backdoor write csr
  task automatic csr_poke(input uvm_object      ptr,
                          input uvm_reg_data_t  value,
                          input uvm_check_e     check = default_csr_check,
                          input bit             predict = 0,
                          input bkdr_reg_path_e kind = BkdrRegPathRtl);
    csr_field_t   csr_or_fld = decode_csr_or_field(ptr);
    uvm_status_e  status;
    string        msg_id = {csr_utils_pkg::msg_id, "::csr_poke"};
    uvm_reg_data_t old_mirrored_val;

    if (csr_or_fld.field != null) begin
      old_mirrored_val = csr_or_fld.field.get_mirrored_value();
      csr_or_fld.field.poke(.status(status), .value(value), .kind(kind.name));
    end else begin
      old_mirrored_val = csr_or_fld.csr.get_mirrored_value();
      csr_or_fld.csr.poke(.status(status), .value(value), .kind(kind.name));
    end
    if (check == UVM_CHECK && status != UVM_IS_OK) begin
      string str;
      uvm_hdl_path_concat paths[$];
      csr_or_fld.csr.get_full_hdl_path(paths, kind.name);
      foreach (paths[0].slices[i]) str = $sformatf("%0s\n%0s", str, paths[0].slices[i].path);
      `uvm_fatal(msg_id, $sformatf("poke failed for %0s, check below paths %0s",
                                   ptr.get_full_name(), str))
    end
    // poke always updates predict value, if predict == 0, revert back to old mirrored value
    if (!predict || kind == BkdrRegPathRtlShadow) begin
      if (csr_or_fld.field != null) begin
        void'(csr_or_fld.field.predict(.value(old_mirrored_val), .kind(UVM_PREDICT_DIRECT),
                                       .path(UVM_BACKDOOR)));
      end else begin
        void'(csr_or_fld.csr.predict(.value(old_mirrored_val), .kind(UVM_PREDICT_DIRECT),
                                     .path(UVM_BACKDOOR)));
      end
    end
  endtask

  task automatic csr_rd(input  uvm_object         ptr, // accept reg or field
                        output uvm_reg_data_t     value,
                        input  uvm_check_e        check = default_csr_check,
                        input  uvm_path_e         path = UVM_DEFAULT_PATH,
                        input  bit                blocking = default_csr_blocking,
                        input  bit                backdoor = 0,
                        input  uint               timeout_ns = default_timeout_ns,
                        input  uvm_reg_map        map = null,
                        input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
    uvm_status_e status;
    if (blocking) begin
      csr_rd_sub(.ptr(ptr), .value(value), .status(status), .check(check), .path(path),
                 .backdoor(backdoor), .timeout_ns(timeout_ns), .map(map), .user_ftdr(user_ftdr));
    end else begin
      `DV_CHECK_EQ(backdoor, 0, "Don't enable backdoor with blocking = 0", error, msg_id)
      fork
        csr_rd_sub(.ptr(ptr), .value(value), .status(status), .check(check), .path(path),
                   .backdoor(backdoor), .timeout_ns(timeout_ns), .map(map), .user_ftdr(user_ftdr));
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_rd, don't use it directly
  task automatic csr_rd_sub(input  uvm_object         ptr, // accept reg or field
                            output uvm_reg_data_t     value,
                            output uvm_status_e       status,
                            input  bit                backdoor = 0,
                            input  uvm_check_e        check = default_csr_check,
                            input  uvm_path_e         path = UVM_DEFAULT_PATH,
                            input  uint               timeout_ns = default_timeout_ns,
                            input  uvm_reg_map        map = null,
                            input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
    if (backdoor) begin
      value = csr_peek(ptr, check);
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
            if (user_ftdr != null) csr_or_fld.csr.set_frontdoor(user_ftdr);
            if (csr_or_fld.field != null) begin
              csr_or_fld.field.read(.status(status), .value(value), .path(path), .map(map),
                                    .prior(100));
            end else begin
              csr_or_fld.csr.read(.status(status), .value(value), .path(path), .map(map),
                                  .prior(100));
            end
            // TODO: need to remove the frontdoor to switch back to the default,
            // but this doesn't work: if (user_ftdr != null) ptr.set_frontdoor(null);
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK,
                           $sformatf("trying to read csr/field %0s", ptr.get_full_name()),
                           error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin
            `DV_WAIT_TIMEOUT(timeout_ns, msg_id,
                             $sformatf("Timeout waiting to csr_rd %0s (addr=0x%0h)",
                                       ptr.get_full_name(), csr_or_fld.csr.get_address()))
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  // backdoor read csr
  // uvm_reg::peek() returns a 2-state value, directly get data from hdl path
  function automatic uvm_reg_data_t csr_peek(uvm_object      ptr,
                                             uvm_check_e     check = default_csr_check,
                                             bkdr_reg_path_e kind = BkdrRegPathRtl);
    string         msg_id = {csr_utils_pkg::msg_id, "::csr_peek"};
    csr_field_t    csr_or_fld = decode_csr_or_field(ptr);
    uvm_reg        csr = csr_or_fld.csr;
    uvm_reg_data_t value = 0;

    uvm_hdl_path_concat paths[$];
    csr.get_full_hdl_path(paths, kind.name);

    `DV_CHECK_FATAL(paths.size() > 0,
                    $sformatf("No backdoor defined for %0s path's %0s",
                              csr.get_full_name(), kind.name),
                    msg_id)

    foreach (paths[0].slices[i]) begin
      uvm_reg_data_t field_val;
      `DV_CHECK_FATAL(uvm_hdl_read(paths[0].slices[i].path, field_val),
                      $sformatf("Failed to read %s, slice %d, at path %s",
                                csr.get_full_name(), i, paths[0].slices[i].path),
                      msg_id)
      if (check == UVM_CHECK) `DV_CHECK_EQ($isunknown(field_val), 0, "", error, msg_id)

      value |= field_val << paths[0].slices[i].offset;
    end

    // We now have the contents of the field or register in value. If ptr was a sub-field of some
    // register, it will be laid out in the same way as the field is laid out in the register.
    // That's no problem: we can just extract the relevant field from the laid-out value here.
    if (csr_or_fld.field != null) value = get_field_val(csr_or_fld.field, value);

    return value;
  endfunction

  task automatic csr_rd_check(input  uvm_object         ptr,
                              input  uvm_check_e        check = default_csr_check,
                              input  uvm_path_e         path = UVM_DEFAULT_PATH,
                              input  bit                blocking = default_csr_blocking,
                              input  bit                backdoor = 0,
                              input  uint               timeout_ns = default_timeout_ns,
                              input  bit                compare = 1'b1,
                              input  bit                compare_vs_ral = 1'b0,
                              input  uvm_reg_data_t     compare_mask = '1,
                              input  uvm_reg_data_t     compare_value = 0,
                              input  string             err_msg = "",
                              input  uvm_reg_map        map = null,
                              input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
    fork
      begin : isolation_fork
        fork
          begin
            csr_field_t     csr_or_fld;
            uvm_status_e    status;
            uvm_reg_data_t  obs;
            uvm_reg_data_t  exp;
            uvm_reg_data_t  reset_val;
            string          msg_id = {csr_utils_pkg::msg_id, "::csr_rd_check"};

            csr_or_fld = decode_csr_or_field(ptr);

            csr_rd_sub(.ptr(ptr), .value(obs), .status(status), .check(check), .path(path),
                       .backdoor(backdoor), .timeout_ns(timeout_ns), .map(map),
                       .user_ftdr(user_ftdr));

            // get mirrored value after read to make sure the read reg access is updated
            if (csr_or_fld.field != null) begin
              exp = csr_or_fld.field.get_mirrored_value();
              reset_val = csr_or_fld.field.get_reset();
            end else begin
              exp = csr_or_fld.csr.get_mirrored_value();
              reset_val = csr_or_fld.csr.get_reset();
            end
            if (compare && status == UVM_IS_OK && !under_reset) begin
              obs = obs & compare_mask;
              exp = (compare_vs_ral ? exp : compare_value) & compare_mask;
              `DV_CHECK_EQ(obs, exp, $sformatf("Regname: %0s reset value: 0x%0h %0s",
                                               ptr.get_full_name(), reset_val, err_msg),
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
                                          input csr_excl_item   csr_excl_item = get_excl_item(csr));
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
  task automatic csr_spinwait(input uvm_object          ptr,
                              input uvm_reg_data_t      exp_data,
                              input uvm_check_e         check = default_csr_check,
                              input uvm_path_e          path = UVM_DEFAULT_PATH,
                              input uvm_reg_map         map = null,
                              input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor,
                              input uint                spinwait_delay_ns = 0,
                              input uint                timeout_ns = default_spinwait_timeout_ns,
                              input compare_op_e        compare_op = CompareOpEq,
                              input bit                 backdoor = 0,
                              input uvm_verbosity       verbosity = UVM_HIGH);
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
            `uvm_info("csr_utils_pkg", "In csr_spinwait", verbosity)
            csr_rd(.ptr(ptr), .value(read_data), .check(check), .path(path),
                   .blocking(1), .map(map), .user_ftdr(user_ftdr), .backdoor(backdoor));
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
            `DV_WAIT_TIMEOUT(timeout_ns, msg_id, $sformatf("timeout %0s (addr=0x%0h) == 0x%0h",
                ptr.get_full_name(), csr_or_fld.csr.get_address(), exp_data))
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask

  task automatic mem_rd(input  uvm_mem            ptr,
                        input  int                offset,
                        output bit[31:0]          data,
                        input  uvm_check_e        check = default_csr_check,
                        input  bit                blocking = default_csr_blocking,
                        input  uint               timeout_ns = default_timeout_ns,
                        input  uvm_reg_map        map = null,
                        input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
    if (blocking) begin
      mem_rd_sub(ptr, offset, data, check, timeout_ns, map, user_ftdr);
    end else begin
      fork
        mem_rd_sub(ptr, offset, data, check, timeout_ns, map, user_ftdr);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask : mem_rd

  task automatic mem_rd_sub(input  uvm_mem            ptr,
                            input  int                offset,
                            output bit[31:0]          data,
                            input  uvm_check_e        check = default_csr_check,
                            input  uint               timeout_ns = default_timeout_ns,
                            input  uvm_reg_map        map = null,
                            input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
    fork
      begin : isolating_fork
        uvm_status_e status;
        string       msg_id = {csr_utils_pkg::msg_id, "::mem_rd"};

        fork
          begin
            increment_outstanding_access();
            if (user_ftdr != null) ptr.set_frontdoor(user_ftdr);
            ptr.read(.status(status), .offset(offset), .value(data), .map(map), .prior(100));
            // TODO: need to remove the frontdoor to switch back to the default,
            // but this doesn't work: if (user_ftdr != null) ptr.set_frontdoor(null);
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK,
                           $sformatf("trying to read mem %0s", ptr.get_full_name()), error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin : mem_rd_timeout
            `DV_WAIT_TIMEOUT(timeout_ns, msg_id,
                             $sformatf("Timeout waiting to mem_rd %0s (addr=0x%0h)",
                                       ptr.get_full_name(), offset))
          end
        join_any
        disable fork;
      end : isolating_fork
    join
  endtask : mem_rd_sub

  task automatic mem_wr(input uvm_mem             ptr,
                        input int                 offset,
                        input bit[31:0]           data,
                        input bit                 blocking = default_csr_blocking,
                        input uint                timeout_ns = default_timeout_ns,
                        input uvm_check_e         check = default_csr_check,
                        input uvm_reg_map         map = null,
                        input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
    if (blocking) begin
      mem_wr_sub(ptr, offset, data, timeout_ns, check, map, user_ftdr);
    end else begin
      fork
        mem_wr_sub(ptr, offset, data, timeout_ns, check, map, user_ftdr);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask : mem_wr

  task automatic mem_wr_sub(input uvm_mem             ptr,
                            input int                 offset,
                            input bit[31:0]           data,
                            input uint                timeout_ns = default_timeout_ns,
                            input uvm_check_e         check = default_csr_check,
                            input uvm_reg_map         map = null,
                            input  uvm_reg_frontdoor  user_ftdr = default_user_frontdoor);
     fork
      begin : isolation_fork
        uvm_status_e status;
        string       msg_id = {csr_utils_pkg::msg_id, "::mem_wr"};

        fork
          begin
            increment_outstanding_access();
            if (user_ftdr != null) ptr.set_frontdoor(user_ftdr);
            ptr.write(.status(status), .offset(offset), .value(data), .map(map), .prior(100));
            // TODO: need to remove the frontdoor to switch back to the default,
            // but this doesn't work: if (user_ftdr != null) ptr.set_frontdoor(null);
            if (check == UVM_CHECK && !under_reset) begin
              `DV_CHECK_EQ(status, UVM_IS_OK,
                           $sformatf("trying to write mem %0s", ptr.get_full_name()),
                           error, msg_id)
            end
            decrement_outstanding_access();
          end
          begin
            `DV_WAIT_TIMEOUT(timeout_ns, msg_id,
                             $sformatf("Timeout waiting to mem_wr %0s (addr=0x%0h)",
                                       ptr.get_full_name(), offset))
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
                                                         csr_excl_item m_csr_excl_item =
                                                                       get_excl_item(csr));
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

  // Returns the write data value masked with excluded fields.
  //
  // Some fields in the CSR may be excluded from writes. In that case, we need to revert those
  // fields to their mirrored values and write the rest of the fields with the given value.
  function automatic uvm_reg_data_t get_csr_wdata_with_write_excl(
      uvm_reg         csr,
      uvm_reg_data_t  wdata,
      csr_test_type_e csr_test_type,
      csr_excl_item   m_csr_excl_item = get_excl_item(csr)
  );
    uvm_reg_field flds[$];
    csr.get_fields(flds);

    foreach (flds[i]) begin
      if (m_csr_excl_item.is_excl(flds[i], CsrExclWrite, csr_test_type)) begin
        `uvm_info(msg_id, $sformatf(
                  "Retain mirrored value 0x%0h for field %0s due to CsrExclWrite exclusion",
                  `gmv(flds[i]), flds[i].get_full_name()), UVM_MEDIUM)
        wdata = get_csr_val_with_updated_field(flds[i], wdata, `gmv(flds[i]));
      end
    end
    return wdata;
  endfunction

  // Returns the CSR exclusion item associated with the provided object.
  //
  // If an exclusion item for the immediate block (parent of the CSR if ptr is a CSR or a field) is
  // not found, it recurses through the block's ancestors to find an available exclusion item.
  // arg ptr: An extention of one of dv_base_reg{, _block or _field} classes.
  function automatic csr_excl_item get_excl_item(uvm_object ptr);
    dv_base_reg_block blk;

    // Attempt cast to blk. If it fails, then attempt to cast to CSR or field.
    if (!$cast(blk, ptr)) begin
      csr_field_t csr_or_fld = decode_csr_or_field(ptr);
      `downcast(blk, csr_or_fld.csr.get_parent(), , , msg_id)
    end

    // Recurse through block's ancestors.
    do begin
      csr_excl_item csr_excl = blk.get_excl_item();
      if (csr_excl != null) return csr_excl;
      `downcast(blk, blk.get_parent(), , , msg_id)
    end while (blk != null);
    return null;
  endfunction

  // Clone a UVM address map
  function automatic uvm_reg_map clone_reg_map(
      string name, uvm_reg_map map, uvm_reg_addr_t base_addr = 0, int n_bytes = 4,
      uvm_endianness_e endian = UVM_LITTLE_ENDIAN, bit byte_addressing = 1);
    uvm_reg_map clone;
    uvm_reg_map submaps[$];
    uvm_reg regs[$];
    uvm_reg_block blk;
    uvm_mem mems[$];

    // Clone the map
    blk = map.get_parent();
    clone = blk.create_map(
        .name(name),
        .base_addr(base_addr),
        .n_bytes(n_bytes),
        .endian(endian),
        .byte_addressing(byte_addressing)
    );

    // Clone the submaps by calling this function recursively
    map.get_submaps(submaps);
    while (submaps.size()) begin
      uvm_reg_map submap, submap_clone;
      submap = submaps.pop_front();
      submap_clone = clone_reg_map(.name(name), .map(submap), .base_addr(submap.get_base_addr()),
        // Use `UVM_NO_HIER` argument to get the n_bytes from the submap instead of the system
        // level value.
        .n_bytes(submap.get_n_bytes(UVM_NO_HIER)), .endian(endian));
      clone.add_submap(.child_map(submap_clone), .offset(map.get_submap_offset(submap)));
    end

    // Clone the registers
    map.get_registers(regs, UVM_NO_HIER);
    while (regs.size()) begin
      uvm_reg rg;
      rg = regs.pop_front();
      clone.add_reg(.rg(rg), .offset(rg.get_offset(map)), .rights(rg.get_rights(map)), .unmapped(0),
                    .frontdoor(null));
    end

    // Clone the memories
    map.get_memories(mems, UVM_NO_HIER);
    while (mems.size()) begin
      uvm_mem mem;
      mem = mems.pop_front();
      clone.add_mem(.mem(mem), .offset(mem.get_offset(0, map)), .rights(mem.get_rights(map)),
                    .unmapped(0), .frontdoor(null));
    end
    return clone;

  endfunction

  // sources
  `include "csr_seq_lib.sv"

endpackage
