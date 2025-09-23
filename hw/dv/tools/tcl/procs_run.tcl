# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################################################################
#
# Library of helper procedures for running.
#
################################################################################

proc run_to_completion_and_exit {} {
  # Run to completion.
  run

  # Xcelium provides a `finish` tcl command instead of `quit`. The argument '2'
  # enables the logging of additional resource usage information.
  global simulator
  if {$simulator eq "xcelium"} {finish 2}

  # Most simulators provide a 'quit' procedure which wraps exit with some
  # tool-specific cleanup operations.
  quit
}
