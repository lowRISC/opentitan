// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface irq_if;
  logic        clock;
  logic        reset;
  logic        irq_software;
  logic        irq_timer;
  logic        irq_external;
  logic [14:0] irq_fast;
  logic        irq_nm;       // non-maskeable interrupt
endinterface
