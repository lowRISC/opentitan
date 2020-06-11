// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_oldval_test extends ibex_icache_base_test;

  `uvm_component_utils(ibex_icache_oldval_test)
  `uvm_component_new

  // At end-of-test, look at the counters to see how often we've seen a value that isn't the most
  // recent result possible. Check that possible_old_count is big enough to exclude statistical
  // weirdness (arbitrarily taken as 1000 for now) and that check that at least 5% of these fetches
  // did indeed get an "old" result. This is a really low-ball figure, but is enough to check that
  // the cache does occasionally store an old result across a disable/enable cycle.
  //
  // Note that we can't do this in the scoreboard itself, because it only makes sense when we know
  // that we're doing lots of caching
  function void check_phase(uvm_phase phase);
    int unsigned actual, possible;
    int unsigned frac4;

    super.check_phase(phase);

    actual = env.scoreboard.actual_old_count;
    possible = env.scoreboard.possible_old_count;

    `DV_CHECK(possible >= 1000,
              $sformatf({"After an oldval test, we only saw %0d points where we ",
                         "could have returned an old value."},
                        possible))

    // Calculate a percentage to report with a decimal place (especially helpful if we fail).
    `DV_CHECK_LE_FATAL(actual, possible);
    frac4 = (1000 * actual + (possible / 2)) / possible;

    `DV_CHECK(frac4 >= 50,
              $sformatf({"After an oldval test with %0d possible points for an old value, we got ",
                         "one %0d times (%0d.%0d%%). This is less than the 5% minimum threshold."},
                        possible, actual, frac4 / 10, frac4 % 10))

  endfunction : check_phase

endclass : ibex_icache_oldval_test

