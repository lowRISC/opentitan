// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class: csr_excl_item
// Description: CSR exclusion item that holds exclusions applied for a given set of blocks /
// registers / fields provided and maintained as strings.
class csr_excl_item extends uvm_object;
  `uvm_object_utils(csr_excl_item)

  typedef struct {
    bit             enable;
    int             csr_test_type;
    csr_excl_type_e csr_excl_type;
  } csr_excl_s;
  local csr_excl_s exclusions[string];

  `uvm_object_new

  // Adds an exclusion for an individual block, register or field.
  //
  // arg obj: Hierarchical path to the block, csr or field as string. Passing * and ? wildcards for
  //          glob style matching is allowed. User needs to take care the wildcards don't match more
  //          than desired. For example, for the ral.ctrl.tx field:
  //          obj = "ral.ctrl.tx" or "*.ctrl.tx" should work; "*.tx" might be too generic.
  // arg csr_excl_type: The desired exclusion type.
  // arg csr_test_type: The desired test type for which the exclusion is in effect.
  virtual function void add_excl(string obj,
                                 csr_excl_type_e csr_excl_type,
                                 csr_test_type_e csr_test_type = CsrAllTests);
    bit [2:0] val = CsrNoExcl;
    bit [NUM_CSR_TESTS-1:0] test = CsrInvalidTest;

    `DV_CHECK_NE_FATAL(csr_test_type, CsrInvalidTest,
                       $sformatf("Test type not specified for the exclusion of %0s.", obj))

    if (!exclusions.exists(obj)) begin
      exclusions[obj] = '{enable:1'b1, csr_test_type:csr_test_type, csr_excl_type:csr_excl_type};
      return;
    end

    val = csr_excl_type | exclusions[obj].csr_excl_type;
    test = csr_test_type | exclusions[obj].csr_test_type;
    exclusions[obj].csr_excl_type = csr_excl_type_e'(val);
    exclusions[obj].csr_test_type = test;
  endfunction

  // Turns exclusion on or off for a block, register or field.
  //
  // The originally set exclusions are untouched. This method only enables or disables the
  // application of the exclusions temporarily.
  //
  // obj: The hierarchical path to block, register or field.
  // enable: Bit indicating whether to enable or disable the application of exclusion.
  // throw_error: Bit indicating whether to throw error if exclusions associated with obj do not
  // exist.
  virtual function void enable_excl(string obj, bit enable = 1'b1, bit throw_error = 1'b1);
    string index;
    if (get_excl_index(obj, index)) begin
      exclusions[index].enable = enable;
      return;
    end
    if (throw_error) begin
      `uvm_fatal(`gfn, $sformatf("No exclusions found for %0s.", obj))
    end
  endfunction

  // Checks if the given block, register or field is excluded.
  //
  // arg obj: The given block, register or field.
  // arg csr_excl_type: The exclusion checked against.
  // arg csr_test_type: The type of test for which the exclusion is in effect.
  function bit is_excl(uvm_object obj,
                       csr_excl_type_e csr_excl_type,
                       csr_test_type_e csr_test_type);
    uvm_reg_block blk;

    // Attempt cast to block. If it fails, then attempt to cast to CSR or field.
    if (!$cast(blk, obj)) begin
      csr_field_t csr_or_fld = decode_csr_or_field(obj);
      if (csr_or_fld.field != null) begin
        if (has_excl(csr_or_fld.field.`gfn, csr_excl_type, csr_test_type, is_excl)) return is_excl;
      end else begin
        if (has_excl(csr_or_fld.csr.`gfn, csr_excl_type, csr_test_type, is_excl)) return is_excl;
      end
      `downcast(blk, csr_or_fld.csr.get_parent(), , , msg_id)
    end

    // Recurse through block's ancestors.
    do begin
      if (has_excl(blk.`gfn, csr_excl_type, csr_test_type, is_excl)) return is_excl;
      blk = blk.get_parent();
    end while (blk != null);
    return 1'b0;
  endfunction

  // Retrieves the string index of the exclusions data structure.
  //
  // The provided object for lookup is a string itself. It however, may or may
  // not exist verbatim as an associative array index in the `exclusions` data
  // structure, since glob-style wildcards are supported when adding the
  // exclusions. The provided object must hence be a fully resolved
  // hierarchical path to the CSR block, register or field.
  //
  // Returns 1 if index is found, else 0.
  // Returns the actual index as output arg.
  local function bit get_excl_index(input string obj, output string index);
    // If obj is a index of exclusions, return it, else loop through available
    // keys to find a glob match.
    if (exclusions.exists(obj)) begin
      index = obj;
      return 1'b1;
    end else begin
      foreach (exclusions[str]) begin
        if (!uvm_re_match(str, obj)) begin
          index = str;
          return 1'b1;
        end
      end
    end
    return 1'b0;
  endfunction

  // Checks if a particular exclusion for an object for a test is in effect.
  //
  // arg obj: The given block, register or field as string lookup.
  // arg csr_excl_type: The exclusion checked against.
  // arg csr_test_type: The type of test for which the exclusion is in effect.
  // arg is_excl: Bit indicating the object is excluded.
  //
  // Returns 1 if an associated exclusion is found, else 0.
  local function bit has_excl(input string obj,
                              input csr_excl_type_e csr_excl_type,
                              input csr_test_type_e csr_test_type,
                              output bit is_excl);
    string index;
    if (get_excl_index(obj, index)) begin
      is_excl = exclusions[index].enable &&
                ((exclusions[index].csr_test_type & csr_test_type) != CsrInvalidTest) &&
                ((exclusions[index].csr_excl_type & csr_excl_type) != CsrNoExcl);
      return 1'b1;
    end
    return 1'b0;
  endfunction

  // Prints all exclusions for ease of debug.
  virtual function void print_exclusions(uvm_verbosity verbosity = UVM_HIGH);
    string test_names;
    for (int i = NUM_CSR_TESTS - 1; i >= 0; i--) begin
      csr_test_type_e csr_test = csr_test_type_e'(1 << i);
      test_names = {test_names, csr_test.name(),  (i > 0) ? " " : ""};
    end
    foreach (exclusions[item]) begin
      string enabled = exclusions[item].enable ? "[enabled]" : "[disabled]";
      `uvm_info(`gfn, $sformatf("CSR/field [%s] exclusion %s %s in csr_tests: {%s} = {%0b}",
                                item, exclusions[item].csr_excl_type.name(), enabled, test_names,
                                exclusions[item].csr_test_type), verbosity)
    end
  endfunction

endclass
