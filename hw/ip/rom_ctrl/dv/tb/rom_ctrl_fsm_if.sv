// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is designed to be bound into rom_ctrl_fsm. This can then look at internal
// information from the fsm and expose it cleanly. There are no ports: interactions with internal
// signals all work by upwards name references.

interface rom_ctrl_fsm_if ();

endinterface
