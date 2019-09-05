// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csr_utils_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types and variables
  uint       outstanding_csr_accesses    = 0;
  uint       default_timeout_ns          = 1_000_000; // 1ms
  uint       default_spinwait_timeout_ns = 10_000_000; // 10ms
  string     msg_id                      = "csr_utils";
  bit        default_csr_blocking        = 1;

  // csr field struct - hold field specific params
  typedef struct {
    uvm_reg         csr;
    uvm_reg_field   field;
    uvm_reg_data_t  mask;
    uint            shift;
  } csr_field_s;

  // csr exclusion indications
  typedef enum bit[2:0] {
    CsrNoExcl         = 3'b000, // no exclusions
    CsrExclInitCheck  = 3'b001, // exclude csr from init val check
    CsrExclWriteCheck = 3'b010, // exclude csr from write-read check
    CsrExclCheck      = 3'b011, // exclude csr from init or write-read check
    CsrExclWrite      = 3'b100, // exclude csr from write
    CsrExclAll        = 3'b111  // exclude csr from init or write or writ-read check
  } csr_excl_type_e;

  // Get all valid csr addrs - useful to check if incoming addr falls in the csr range.
  function automatic void get_csr_addrs(input uvm_reg_block ral, ref uvm_reg_addr_t csr_addrs[$]);
    uvm_reg csrs[$];
    ral.get_registers(csrs);
    csr_addrs.delete();
    foreach (csrs[i]) begin
      csr_addrs.push_back(csrs[i].get_address());
    end
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
  // is successful on either, then set the appropriate csr_field_s return values.
  function automatic csr_field_s decode_csr_or_field(input uvm_object ptr);
    uvm_reg       csr;
    uvm_reg_field fld;
    csr_field_s   result;
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
                            input  uvm_check_e  check = UVM_CHECK,
                            input  uvm_path_e   path = UVM_DEFAULT_PATH,
                            input  bit          blocking = default_csr_blocking,
                            input  uint         timeout_ns = default_timeout_ns,
                            input  uvm_reg_map  map = null);
    if (blocking) begin
      csr_update_sub(csr, check, path, timeout_ns, map);
    end else begin
      fork
        csr_update_sub(csr, check, path, timeout_ns, map);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_update, don't use it directly
  task automatic csr_update_sub(input  uvm_reg      csr,
                                input  uvm_check_e  check = UVM_CHECK,
                                input  uvm_path_e   path = UVM_DEFAULT_PATH,
                                input  uint         timeout_ns = default_timeout_ns,
                                input  uvm_reg_map  map = null);
    fork
      begin : isolation_fork
        uvm_status_e  status;
        string        msg_id = {csr_utils_pkg::msg_id, "::csr_update"};

        fork
          begin
            outstanding_csr_accesses++;
            csr.update(.status(status), .path(path), .map(map));
            if (check == UVM_CHECK) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            outstanding_csr_accesses--;
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
                        input uvm_check_e    check = UVM_CHECK,
                        input uvm_path_e     path = UVM_DEFAULT_PATH,
                        input  bit           blocking = default_csr_blocking,
                        input uint           timeout_ns = default_timeout_ns,
                        input uvm_reg_map    map = null);
    if (blocking) begin
      csr_wr_sub(csr, value, check, path, timeout_ns, map);
    end else begin
      fork
        csr_wr_sub(csr, value, check, path, timeout_ns, map);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_wr, don't use it directly
  task automatic csr_wr_sub(input uvm_reg        csr,
                            input uvm_reg_data_t value,
                            input uvm_check_e    check = UVM_CHECK,
                            input uvm_path_e     path = UVM_DEFAULT_PATH,
                            input uint           timeout_ns = default_timeout_ns,
                            input uvm_reg_map    map = null);
    fork
      begin : isolation_fork
        uvm_status_e  status;
        string        msg_id = {csr_utils_pkg::msg_id, "::csr_wr"};

        fork
          begin
            outstanding_csr_accesses++;
            csr.write(.status(status), .value(value), .path(path), .map(map));
            if (check == UVM_CHECK) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            outstanding_csr_accesses--;
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

  task automatic csr_rd(input  uvm_object     ptr, // accept reg or field
                        output uvm_reg_data_t value,
                        input  uvm_check_e    check = UVM_CHECK,
                        input  uvm_path_e     path = UVM_DEFAULT_PATH,
                        input  bit            blocking = default_csr_blocking,
                        input  uint           timeout_ns = default_timeout_ns,
                        input  uvm_reg_map    map = null);
    if (blocking) begin
      csr_rd_sub(ptr, value, check, path, timeout_ns, map);
    end else begin
      fork
        csr_rd_sub(ptr, value, check, path, timeout_ns, map);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  // subroutine of csr_rd, don't use it directly
  task automatic csr_rd_sub(input  uvm_object     ptr, // accept reg or field
                            output uvm_reg_data_t value,
                            input  uvm_check_e    check = UVM_CHECK,
                            input  uvm_path_e     path = UVM_DEFAULT_PATH,
                            input  uint           timeout_ns = default_timeout_ns,
                            input  uvm_reg_map    map = null);
    fork
      begin : isolation_fork
        csr_field_s   csr_or_fld;
        uvm_status_e  status;
        string        msg_id = {csr_utils_pkg::msg_id, "::csr_rd"};

        fork
          begin
            outstanding_csr_accesses++;
            csr_or_fld = decode_csr_or_field(ptr);
            if (csr_or_fld.field != null) begin
              csr_or_fld.field.read(.status(status), .value(value), .path(path), .map(map));
            end else begin
              csr_or_fld.csr.read(.status(status), .value(value), .path(path), .map(map));
            end
            if (check == UVM_CHECK) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            outstanding_csr_accesses--;
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

  task automatic csr_rd_check(input  uvm_object     ptr,
                              input  uvm_check_e    check = UVM_CHECK,
                              input  uvm_path_e     path = UVM_DEFAULT_PATH,
                              input  bit            blocking = default_csr_blocking,
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
            csr_field_s     csr_or_fld;
            uvm_status_e    status;
            uvm_reg_data_t  obs;
            uvm_reg_data_t  exp;
            string          msg_id = {csr_utils_pkg::msg_id, "::csr_rd_check"};

            outstanding_csr_accesses++;
            csr_or_fld = decode_csr_or_field(ptr);
            // get mirrored value before the read
            if (csr_or_fld.field != null) begin
              exp = csr_or_fld.field.get_mirrored_value();
            end else begin
              exp = csr_or_fld.csr.get_mirrored_value();
            end
            csr_rd(.ptr(ptr), .value(obs), .check(check), .path(path),
                   .blocking(1), .timeout_ns(timeout_ns), .map(map));
            if (compare) begin
              obs = obs & compare_mask;
              exp = (compare_vs_ral ? exp : compare_value) & compare_mask;
              `DV_CHECK_EQ(obs, exp, err_msg, error, msg_id)
            end
            outstanding_csr_accesses--;
          end
        join_none
        if (blocking) wait fork;
        // Add #0 to ensure that this thread starts executing before any subsequent call
        else #0;
      end : isolation_fork
    join
  endtask



  // poll a csr or csr field continuously until it reads the expected value.
  task automatic csr_spinwait(input uvm_object      ptr,
                              input uvm_reg_data_t  exp_data,
                              input uvm_check_e     check = UVM_CHECK,
                              input uvm_path_e      path = UVM_DEFAULT_PATH,
                              input uvm_reg_map     map = null,
                              input uint            spinwait_delay_ns = 0,
                              input uint            timeout_ns = default_spinwait_timeout_ns,
                              input compare_op_e    compare_op = CompareOpEq,
                              input uvm_verbosity   verbosity = UVM_HIGH);
    fork
      begin : isolation_fork
        csr_field_s     csr_or_fld;
        uvm_reg_data_t  read_data;
        string          msg_id = {csr_utils_pkg::msg_id, "::csr_spinwait"};

        csr_or_fld = decode_csr_or_field(ptr);
        fork
          while (1) begin
            if (spinwait_delay_ns) #(spinwait_delay_ns * 1ns);
            csr_rd(.ptr(ptr), .value(read_data), .check(check), .path(path),
                   .blocking(1), .map(map));
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
                        input  uvm_check_e check = UVM_CHECK,
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
                            input  uvm_check_e check = UVM_CHECK,
                            input  uint        timeout_ns = default_timeout_ns,
                            input  uvm_reg_map map = null);
    fork
      begin : isolating_fork
        uvm_status_e status;
        string       msg_id = {csr_utils_pkg::msg_id, "::mem_rd"};

        fork
          begin
            outstanding_csr_accesses++;
            ptr.read(.status(status), .offset(offset), .value(data), .map(map));
            if (check == UVM_CHECK) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            outstanding_csr_accesses--;
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
                        input uvm_check_e check = UVM_CHECK,
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
                            input uvm_check_e check = UVM_CHECK,
                            input uvm_reg_map map = null);
     fork
      begin : isolation_fork
        uvm_status_e status;
        string       msg_id = {csr_utils_pkg::msg_id, "::mem_wr"};

        fork
          begin
            outstanding_csr_accesses++;
            ptr.write(.status(status), .offset(offset), .value(data), .map(map));
            if (check == UVM_CHECK) begin
              `DV_CHECK_EQ(status, UVM_IS_OK, "", error, msg_id)
            end
            outstanding_csr_accesses--;
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

  // sources
  `include "csr_excl_item.sv"
  `include "csr_seq_lib.sv"

endpackage
