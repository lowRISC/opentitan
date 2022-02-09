// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// coverage object for a fixed width mubi
class mubi_cov #(parameter int Width = 4,
                parameter int ValueTrue = prim_mubi_pkg::MuBi4True,
                parameter int ValueFalse = prim_mubi_pkg::MuBi4False
                ) extends uvm_object;
  `uvm_object_param_utils(mubi_cov #(Width, ValueTrue, ValueFalse))

  // Collect true, false and at least N other values (N = Width)
  covergroup mubi_cg(string name) with function sample(bit [Width-1:0] value);
    option.per_instance = 1;
    option.name         = name;

    cp_value: coverpoint value {
      bins true = {ValueTrue};
      bins false = {ValueFalse};
      bins others[Width] = {[0:{Width{1'b1}}]} with (!(item inside {ValueTrue, ValueFalse}));
    }
  endgroup : mubi_cg

  // use reg_field name as this name
  function new(string name = "");
    mubi_cg = new($sformatf("mubi%0d_cov_of_%s", Width, name));
  endfunction : new

  virtual function void sample(bit [Width-1:0] value);
    mubi_cg.sample(value);
  endfunction : sample
endclass : mubi_cov

typedef mubi_cov #(.Width(4),
                   .ValueTrue(prim_mubi_pkg::MuBi4True),
                   .ValueFalse(prim_mubi_pkg::MuBi4False)) mubi4_cov;
typedef mubi_cov #(.Width(8),
                   .ValueTrue(prim_mubi_pkg::MuBi8True),
                   .ValueFalse(prim_mubi_pkg::MuBi8False)) mubi8_cov;
typedef mubi_cov #(.Width(12),
                   .ValueTrue(prim_mubi_pkg::MuBi12True),
                   .ValueFalse(prim_mubi_pkg::MuBi12False)) mubi12_cov;
typedef mubi_cov #(.Width(16),
                   .ValueTrue(prim_mubi_pkg::MuBi16True),
                   .ValueFalse(prim_mubi_pkg::MuBi16False)) mubi16_cov;

// a mubi coverage object, which allows to dynamically select the width of mubi
class dv_base_mubi_cov extends uvm_object;
  int mubi_width = 0;

  // declare all mubi types, but only one will be created
  mubi4_cov m_mubi4_cov;
  mubi8_cov m_mubi8_cov;
  mubi12_cov m_mubi12_cov;
  mubi16_cov m_mubi16_cov;

  `uvm_object_utils(dv_base_mubi_cov)
  `uvm_object_new

  // use reg_field name as this name
  function void create_cov(int mubi_width);
    string cov_name = $sformatf("mubi%0d_cov_of_%s", mubi_width, `gfn);

    // create_cov can be invoked only once
    `DV_CHECK_EQ(this.mubi_width, 0)
    this.mubi_width = mubi_width;

    case (mubi_width)
      4:  m_mubi4_cov  = mubi4_cov::type_id::create(cov_name);
      8:  m_mubi8_cov  = mubi8_cov::type_id::create(cov_name);
      12: m_mubi12_cov = mubi12_cov::type_id::create(cov_name);
      16: m_mubi16_cov = mubi16_cov::type_id::create(cov_name);
      default: `uvm_fatal(`gfn, $sformatf("Unsupported mubi width (%0d) is used", mubi_width))
    endcase
  endfunction : create_cov

  virtual function void sample(int value);
    case (mubi_width)
      4:  m_mubi4_cov.sample(value);
      8:  m_mubi8_cov.sample(value);
      12: m_mubi12_cov.sample(value);
      16: m_mubi16_cov.sample(value);
      default: `uvm_fatal(`gfn, $sformatf("Unsupported mubi width (%0d) is used", mubi_width))
    endcase
  endfunction : sample
endclass : dv_base_mubi_cov


