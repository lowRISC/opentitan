# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################################################################
#
# Library of helper procedures.
#
################################################################################

# Checks if variable is defined, else throw an error and exit.
proc checkVarExists {var} {
    upvar $var var_
    if {![info exists var_]} {
        puts "ERROR: Variable \"$var\" not found."
        exit
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

# If an UPPERCASE environment variable of the same string as var exists,
# set var to its value.
proc setViaUpcaseEnvVar {var} {
    upvar $var var_
  set var_upper [string toupper $var]
  if {[info exists ::env($var_upper)]} {
    set var_ "$::env($var_upper)"
  }
}

proc setViaUpcaseEnvVarElseError {var} {
  upvar $var var_
  set var_upper [string toupper $var]
  if {[info exists ::env($var_upper)]} {
    set var_ "$::env($var_upper)"
  } else {
    puts "ERROR: Environment variable $var_upper was not provided, and is not optional. Exiting..."
    exit
  }
}

proc setViaUpcaseEnvVarElseWarning {var warning} {
  upvar $var var_
  set var_upper [string toupper $var]
  if {[info exists ::env($var_upper)]} {
    set var_ "$::env($var_upper)"
  } else {
    puts "$warning"
  }
}

proc checkEq {var value} {
  upvar $var var_
  if {$var_ != $value} {
    puts "ERROR: Check failed \"$var\" == \"$value\"!. Actual: \"$var_\"."
    exit
  }
}

proc checkNe {var value} {
  upvar $var var_
  if {$var_ == $value} {
    puts "ERROR: Check failed \"$var\" != \"$value\"!. Actual: \"$var_\"."
    exit
  }
}
