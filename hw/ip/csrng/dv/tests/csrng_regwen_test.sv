// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_regwen_test extends csrng_base_test;

  `uvm_component_utils(csrng_regwen_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

  endfunction
endclass : csrng_regwen_test
