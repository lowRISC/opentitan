// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Some generally useful macros for RTL.

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
