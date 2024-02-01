# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Post elab script, used in GTECH runs to modify the unmapped netlist before
# writing it out.

# Remove the AES block itself, since this flow is only intended to produce a
# GTECH mapping of the wrapper.
remove_design aes_1_1_4
