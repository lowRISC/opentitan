# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################################################################
#
# Xcelium-specific TCL to be sourced for all simulations.
#
################################################################################

# Print all assertions in the $tb_top scope which have been permanently turned off.
puts "INFO: The following assertions are permamently disabled:"
assertion -list -depth all -multiline -permoff $tb_top
