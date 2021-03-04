// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A fragment of SystemVerilog code that is inserted into the ICache. We're using this to emulate
// missing bind support, so this file should do nothing but instantiate a module.
//
// Using a wildcard (.*) for ports allows the testbench to inspect internal signals of the cache.

formal_tb #(
  .BranchPredictor (BranchPredictor),
  .BusWidth        (BusWidth),
  .CacheSizeBytes  (CacheSizeBytes),
  .ICacheECC       (ICacheECC),
  .LineSize        (LineSize),
  .NumWays         (NumWays),
  .BranchCache     (BranchCache),

  .ADDR_W          (ADDR_W),
  .NUM_FB          (NUM_FB),
  .LINE_W          (LINE_W),
  .BUS_BYTES       (BUS_BYTES),
  .BUS_W           (BUS_W),
  .LINE_BEATS      (LINE_BEATS),
  .LINE_BEATS_W    (LINE_BEATS_W)
) tb_i (.*);
