# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is sourced by all supported simulators. The driver scripts
# (dvsim.py) need to make sure that we don't ask for an unsupported
# dumping format (SHM with VCS, for example). The adjoining common.tcl
# must be sourced prior to sourcing this file.

if {[info proc setDefault] ne "setDefault"} {
  puts "ERROR: Please ensure that common.tcl is sourced."
  quit
}

global simulator
global waves
global tb_top

set wavedump_db "waves.$waves"

# TODO: convert this to a proc?
set fid ""
switch $waves {
  "none" {
    puts "INFO: Dumping waves is not enabled."
  }

  "fsdb" {
    if {$simulator eq "xcelium"} {
      call fsdbDumpfile $wavedump_db
    } else {
      fsdbDumpfile $wavedump_db
    }
  }

  "shm" {
    checkEq simulator "xcelium"
    database -open $wavedump_db -default -shm
  }

  "vpd" {
    checkEq simulator "vcs"
    set fid [dump -file $wavedump_db -type VPD]
  }

  "vcd" {
    if {$simulator eq "xcelium"} {
      database -open $wavedump_db -default -vcd
    } else {
      puts "ERROR: Simulator $simulator does not support dumping waves in VCD."
      quit
    }
  }

  "evcd" {
    if {$simulator eq "xcelium"} {
      database -open $wavedump_db -default -evcd
    } else {
      puts "ERROR: Simulator $simulator does not support dumping waves in EVCD."
      quit
    }
  }

  default {
    puts "ERROR: Unknown wave format: ${waves}."
    quit
  }
}

if {$waves ne "none"} {
  puts "INFO: Dumping waves in [string toupper $waves] format to $wavedump_db."
}

# Provides wave-format-agnostic way to set a scope (design heirarchy).
#
# In large designs, dumping waves on the entire hierarchy can significantly slow down the
# simulation. It is useful in that case to only dump the relevant scopes of interest during debug.
#
# scope       : Design / testbench hierarchy to dump waves. Defaults to $tb_top.
# fid         : File ID returned by the dump command in the first step above.
# depth       : Levels in the hierarchy to dump waves. Defaults to 0 (dump all levels).
# fsdb_flags  : Additional string flags passed to fsdbDumpVars. Defaults to "+all".
# probe_flags : Additional string flags passed to probe command (Xcelium). Defaults to "-all".
# dump_flags  : Additional string flags passed to dump command (VCS). Defaults to "-aggregates".
#
# Depending on the need, more such technlogy specific flags can be added in future.
proc wavedumpScope {scope fid {depth 0} {fsdb_flags "+all"} {probe_flags  "-all"}
                    {dump_flags "-aggregates"}} {
  global simulator
  global waves
  global wavedump_db

  switch $waves {
    "none" {
    }

    "fsdb" {
      # The fsdbDumpvars +all command dumps everything: memories, MDAs,
      # structs, unions, power, packed structs. In addition, also dump SVAs.
      if {$simulator eq "xcelium"} {
        call fsdbDumpvars $depth $scope $fsdb_flags
        call fsdbDumpSVA $depth $scope
      } else {
        fsdbDumpvars $depth $scope $fsdb_flags
        fsdbDumpSVA $depth $scope
      }
    }

    "shm" {
      if {$depth == 0} {
        set depth "all"
      }
      probe "$scope" $probe_flags -depth $depth -memories -shm
    }

    "vpd" {
      # The dump command switch -aggregates enables dumping of structs &
      # arrays.
      dump -add "$scope" -fid $fid -depth $depth $dump_flags
    }

    "vcd" {
      if {$simulator eq "xcelium"} {
        if {$depth == 0} {
          set depth "all"
        }
        probe "$scope" $probe_flags -depth $depth -memories -vcd
      }
    }

    "evcd" {
      if {$simulator eq "xcelium"} {
        if {$depth == 0} {
          set depth "all"
        }
        probe "$scope" $probe_flags -depth $depth -evcd
      }
    }

    default {
      puts "ERROR: Unknown wave format: ${waves}."
      quit
    }
  }
  puts "INFO: Dumping waves in scope \"$scope:$depth\"."
}

# Decide whether to dump the entire testbench hierarchy by default.
#
# If this variable is not set externally, it is set to 1 by default here. When set to 1, it adds the
# entire top-level testbench instance for dumping waves. For larger designs, this may slow down the
# simulation. The user can if needed, set it to 0 in the external tcl script that sources this
# script and manually add the hierarchies of interest in there, using the wavedumpScope proc.
setDefault dump_tb_top 1


# By default, add the full test bench scope for wavedump.
if {$dump_tb_top == 1} {
  wavedumpScope $tb_top $fid
}
