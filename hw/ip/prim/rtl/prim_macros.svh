// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Some generally useful macros for RTL.

// Determine if __actual equals __expected with a margin of __allowed_less and __allowed_more, i.e.,
// if __actual is in the interval [__expected - __allowed_less, __expected + __allowed_more], where
// lower and upper bounds are inclusive.
//
// The caller is responsible for ensuring that the data types are such that
// (1) __actual + __allowed_less
// (2) __expected + __allowed_more
// are well defined and do not overflow and
// (3) (1) >= __expected
// (4) __actual <= (2)
// are well defined and meaningful.  Subtractions are deliberately not used, in order to prevent
// underflows.
`define WITHIN_MARGIN(__actual, __expected, __allowed_less, __allowed_more) \
  (((__actual) + (__allowed_less) >= (__expected)) &&                       \
   ((__actual) <= (__expected) + (__allowed_more)))

// Coverage pragmas, used around code for which we want to disable coverage collection.
// Don't forget to add a closing ON pragma after the code to be skipped.
//
// Some notes:
// - The first line is for VCS, the second for xcelium. It is okay to issue both regardless of
//   the tool used.
// - For xcelium it is possible to discriminate between metrics to be disabled as follows
//   //pragma coverage <metric> = on/off
//   where metric can be block | expr | toggle | fsm.

// TODO(https://github.com/chipsalliance/verible/issues/1498) Verible seems to get confused
// by these macros, so the code will inline these directives until this is fixed.
/*
`ifndef PRAGMA_COVERAGE_OFF
`define PRAGMA_COVERAGE_OFF \
/``/VCS coverage off \
/``/ pragma coverage off
`endif

`ifndef PRAGMA_COVERAGE_ON
`define PRAGMA_COVERAGE_ON \
/``/VCS coverage on \
/``/ pragma coverage on
`endif
*/
