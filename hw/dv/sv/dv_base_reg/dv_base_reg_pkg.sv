// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_base_reg_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

   // global paramters for number of csr tests (including memory test)
  parameter uint NUM_CSR_TESTS = 4;
  string msg_id = "dv_base_reg_pkg";

  // csr field struct - hold field specific params
  typedef struct {
    uvm_reg         csr;
    uvm_reg_field   field;
    uvm_reg_data_t  mask;
    uint            shift;
  } csr_field_t;

 // csr exclusion indications
  typedef enum bit [2:0] {
    CsrNoExcl         = 3'b000, // no exclusions
    CsrExclInitCheck  = 3'b001, // exclude csr from init val check
    CsrExclWriteCheck = 3'b010, // exclude csr from write-read check
    CsrExclCheck      = 3'b011, // exclude csr from init or write-read check
    CsrExclWrite      = 3'b100, // exclude csr from write
    CsrExclAll        = 3'b111  // exclude csr from init or write or write-read check
  } csr_excl_type_e;

  // csr test types
  typedef enum bit [NUM_CSR_TESTS-1:0] {
    CsrInvalidTest    = 4'h0,
    // elementary test types
    CsrHwResetTest    = 4'h1,
    CsrRwTest         = 4'h2,
    CsrBitBashTest    = 4'h4,
    CsrAliasingTest   = 4'h8,
    // combinational test types (combinations of the above), used for exclusion tagging
    CsrNonInitTests   = 4'he, // all but HwReset test
    CsrAllTests       = 4'hf  // all tests
  } csr_test_type_e;

  typedef enum bit[2:0] {
    // If it's a shadow reg, BkdrRegPathRtl is the path to committed reg
    BkdrRegPathRtl,          // backdoor path for reg's val in RTL
    BkdrRegPathRtlShadow,    // backdoor path for shadow reg's shadow val in RTL
    BkdrRegPathGls,          // backdoor path for reg's val in GLS
    BkdrRegPathGlsShdow      // backdoor path for shadow reg's shadow val in GLS
  } bkdr_reg_path_e;

  // Forward-declare class types for the functions below.
  typedef class dv_base_reg_block;
  typedef class dv_base_reg;
  typedef class dv_base_reg_field;

  // This function attempts to cast a given uvm_object ptr into uvm_reg or uvm_reg_field. If cast
  // is successful on either, then set the appropriate csr_field_t return values.
  function automatic csr_field_t decode_csr_or_field(input uvm_object ptr);
    uvm_reg       csr;
    uvm_reg_field fld;
    csr_field_t   result;
    string        msg_id = {dv_base_reg_pkg::msg_id, "::decode_csr_or_field"};

    if ($cast(csr, ptr)) begin
      // return csr object with null field; set the mask to the width's all 1s and shift to 0
      result.csr = csr;
      result.mask = (1 << csr.get_n_bits()) - 1;
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

  function automatic void get_flds_from_uvm_object(input uvm_object obj,
                                                   input string msg = "dv_base_reg_pkg",
                                                   ref dv_base_reg_field flds[$]);
    dv_base_reg       csr;
    dv_base_reg_field fld;

    flds.delete();
    if ($cast(csr, obj)) begin
      csr.get_dv_base_reg_fields(flds);
    end else if ($cast(fld, obj)) begin
      flds.push_back(fld);
    end else begin
      `uvm_fatal(msg, $sformatf("obj %0s is not of type uvm_reg or uvm_reg_field",
                      obj.get_full_name()))
    end
  endfunction : get_flds_from_uvm_object

  // mask and shift data to extract the value specific to that supplied field
  function automatic uvm_reg_data_t get_field_val(uvm_reg_field   field,
                                                  uvm_reg_data_t  value);
    uvm_reg_data_t  mask = (1 << field.get_n_bits()) - 1;
    uint            shift = field.get_lsb_pos();
    get_field_val = (value >> shift) & mask;
  endfunction : get_field_val

  // Returns a mask value from the provided fields. All fields must belong to the same CSR.
  function automatic uvm_reg_data_t get_mask_from_fields(uvm_reg_field fields[$]);
    uvm_reg_data_t mask = '0;
    uvm_reg csr;
    if (fields.size() == 0) return '1;
    foreach (fields[i]) begin
      uvm_reg_data_t fmask;
      uint           fshift;
      if (csr == null) csr = fields[i].get_parent();
      else if (csr != fields[i].get_parent()) begin
        `uvm_fatal(msg_id, $sformatf({"The provided fields belong to at least two different CSRs: ",
                                      "%s, %s. All fields must belong to the same CSR"},
                                     fields[i-1].`gfn, fields[i].`gfn))
      end
      fmask = (1 << fields[i].get_n_bits()) - 1;
      fshift = fields[i].get_lsb_pos();
      mask |= fmask << fshift;
    end
    return mask;
  endfunction

  `include "csr_excl_item.sv"
  `include "dv_base_lockable_field_cov.sv"
  `include "dv_base_shadowed_field_cov.sv"
  `include "dv_base_mubi_cov.sv"
  `include "dv_base_reg_field.sv"
  `include "dv_base_reg.sv"
  `include "dv_base_mem.sv"
  `include "dv_base_reg_block.sv"
  `include "dv_base_reg_map.sv"

endpackage
