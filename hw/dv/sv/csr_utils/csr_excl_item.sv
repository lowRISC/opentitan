// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class: csr_excl_item
// Description: CSR exclusion item that holds exclusions applied for a given set of blocks /
// registers / fields provided and maintained as strings.
class csr_excl_item extends uvm_object;
  `uvm_object_utils(csr_excl_item)

  local csr_excl_type_e exclusions[string];

  `uvm_object_new

  // add exclusion for an individual block, csr or field
  // arg obj: this is the hierarchical path name to the block, csr or field - passing * and ?
  // wildcards for glob style matching is allowed. User needs to take care that wildcards does not
  // end up inadvertently matching more that what was desired. Examples:
  // To exclude ral.ctrl.tx field from writes, obj can be "ral.ctrl.tx" or "*.ctrl.tx"; passing
  // "*.tx" might be too generic
  virtual function void add_excl(string obj, csr_excl_type_e csr_excl_type);
    bit [2:0] val = CsrNoExcl;
    val = csr_excl_type | exclusions[obj];
    exclusions[obj] = csr_excl_type_e'(val);
  endfunction

  // function to check if given blk / csr or field AND its parent has been excluded with the
  // supplied exclusion type
  // arg uvm_object obj: given blk, csr or field
  // arg csr_excl_type_e csr_excl_type: exclusion type
  function bit is_excl(uvm_object obj, csr_excl_type_e csr_excl_type);
    uvm_reg_block blk;
    uvm_reg       csr;

    // if supplied obj is a uvm_reg_block or uvm_reg, then its parent is a uvm_reg_block
    // check if obj's parent is excluded
    if ($cast(blk, obj)) begin
      if (blk.get_parent() != null) begin
        blk = blk.get_parent();
        if (has_excl(blk.`gfn, csr_excl_type)) return 1'b1;
      end
    end
    if ($cast(csr, obj)) begin
      blk = csr.get_parent();
      if (has_excl(blk.`gfn, csr_excl_type)) return 1'b1;
    end
    // TODO: check if any parent in the hierarchy above is excluded
    // check if obj is excluded
    return (has_excl(obj.`gfn, csr_excl_type));
  endfunction

  // check if applied string obj has a match in existing exclusions lookup
  // function is to not be called externally
  local function bit has_excl(string obj, csr_excl_type_e csr_excl_type);
    // check if obj exists verbatim
    if (exclusions.exists(obj)) begin
      `uvm_info(`gfn, $sformatf("has_excl: found exact excl match for %0s: %0s",
                                obj, exclusions[obj].name()), UVM_DEBUG)
      // check if bit(s) corresponding to csr_excl_type are set
      if ((exclusions[obj] & csr_excl_type) != CsrNoExcl) return 1'b1;
    end
    else begin
      // attempt glob style matching
      foreach (exclusions[str]) begin
        if (!uvm_re_match(str, obj)) begin
          `uvm_info(`gfn, $sformatf("has_excl: found glob excl match for %0s(%0s): %0s",
                                    obj, str, exclusions[str].name()), UVM_DEBUG)
          // check if bit(s) corresponding to csr_excl_type are set
          if ((exclusions[str] & csr_excl_type) != CsrNoExcl) return 1'b1;
        end
      end
    end
    return 1'b0;
  endfunction

  // print all exclusions for ease of debug (call this ideally after adding all exclusions)
  virtual function void print_exclusions(uvm_verbosity verbosity = UVM_HIGH);
    foreach (exclusions[item]) begin
      `uvm_info(`gfn, $sformatf("CSR/field [%0s] excluded with %0s",
                                item, exclusions[item].name()), verbosity)
    end
  endfunction

endclass
