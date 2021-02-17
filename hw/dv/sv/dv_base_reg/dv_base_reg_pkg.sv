// Copyright lowRISC contributors.
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
    BkdrRegPathRtl,          // backdoor path for reg's val in RTL
    BkdrRegPathRtlCommitted, // backdoor path for shadow reg's committed val in RTL
    BkdrRegPathRtlShadow,    // backdoor path for shadow reg's shadow val in RTL
    BkdrRegPathGls,          // backdoor path for reg's val in GLS
    BkdrRegPathGlsCommitted, // backdoor path for shadow reg's committed val in GLS
    BkdrRegPathGlsShdow      // backdoor path for shadow reg's shadow val in GLS
  } bkdr_reg_path_e;

  typedef class dv_base_reg_block;
  typedef class dv_base_reg;

  `include "csr_excl_item.sv"
  `include "dv_base_reg_field.sv"
  `include "dv_base_reg.sv"
  `include "dv_base_mem.sv"
  `include "dv_base_reg_block.sv"
  `include "dv_base_reg_map.sv"

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
  endfunction

endpackage
