# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Commonly used globals & procs. This file must be sourced first.
set simulator ""
if {[info exists ::env(SIMULATOR)]} {
  set simulator "$::env(SIMULATOR)"
} else {
  puts "ERROR: tool script run without SIMULATOR environment variable."
  quit
}

set waves "none"
if {[info exists ::env(WAVES)]} {
  set waves "$::env(WAVES)"
}

set tb_top "tb"
if {[info exists ::(TB_TOP)]} {
  set tb_top "$::env(TB_TOP)"
  puts "WARNING: TB_TOP environment variable not set - using \"tb\" as the
        top level testbench hierarchy."
}

# Checks if variable is defined, else throw an error and exit.
proc checkVarExists {var} {
  upvar $var var_
  if {![info exists var_]} {
    puts "ERROR: Variable \"$var\" not found."
    quit
  }
}

# If variable is defined, then use it, else set the default value.
proc setDefault {var value} {
  upvar $var var_
  if {[info exists var_]} {
    puts "INFO: \"$var\" is already set to \"$var_\"."
  } else {
    puts "INFO: Setting \"$var\" to \"$value\"."
    set var_ $value
  }
  return $var_
}

proc checkEq {var value} {
  upvar $var var_
  if {$var_ != $value} {
    puts "ERROR: Check failed \"$var\" == \"$value\"!. Actual: \"$var_\"."
    quit
  }
}

proc checkNe {var value} {
  upvar $var var_
  if {$var_ == $value} {
    puts "ERROR: Check failed \"$var\" != \"$value\"!. Actual: \"$var_\"."
    quit
  }
}
