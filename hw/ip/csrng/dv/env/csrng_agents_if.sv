// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface controls the agents connected to CSRNG.
interface csrng_agents_if;

  logic edn_disable;
  logic entropy_src_disable;

  function automatic drive_edn_disable(bit val);
    edn_disable = val;
  endfunction

  function automatic drive_entropy_src_disable(bit val);
    entropy_src_disable = val;
  endfunction

endinterface
