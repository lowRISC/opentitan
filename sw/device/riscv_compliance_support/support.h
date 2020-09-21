// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @brief OpenTitan-specific wrapper for RISC-V Compliance
 *
 * This header provides a single function, `ot_compliance_main`, which is
 * intentionally outside of the `sw/vendor` directory, so changes in OpenTitan
 * libraries do not require generating patches for `riscv-compliance`.
 */

// NOTE: **DO NOT** #include any files here, since that will leak OpenTitan
// library interfaces past the vendoring boundary.

/**
 * Main function for RISC-V Compliance, provided as an out-of-band.
 */
int opentitan_compliance_main(int argc, char **argv);
