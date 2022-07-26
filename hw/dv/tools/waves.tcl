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

# A procedure that provides a wave-format-agnostic way to enable a scope (design heirarchy).
#
# In large designs, dumping waves on the entire hierarchy can significantly slow down the
# simulation. It is useful in that case to only dump the relevant scopes of interest during debug.
#
# waves       : The wave-format (fsdb, shm, vpd, vcd, evcd, etc).
# simulator   : The simulator used for running the simulation (vcs, xcelium, etc).
# scope       : Design / testbench hierarchy to dump waves. Defaults to $tb_top.
# depth       : Levels in the hierarchy to dump waves. Defaults to 0 (dump all levels).
# fsdb_flags  : Additional string flags passed to fsdbDumpVars. Defaults to "+all", which enables
#               dumping of memories, MDAs, structs, unions, power, packed structs, and SVAs.
# probe_flags : Additional string flags passed to probe command (Xcelium). Defaults to "-all".
# dump_flags  : Additional string flags passed to dump command (VCS). Defaults to "-aggregates",
#               which enables dumping of structs and arrays.
#
# Depending on the need, more such technology specific flags can be added in future.
proc wavedumpScope {waves simulator scope {depth 0} {fsdb_flags "+all"} {probe_flags "-all"}
                    {dump_flags "-aggregates"}} {

  switch $waves {
    "none" {
      return
    }

    "fsdb" {
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
      global vpd_fid
      dump -add "$scope" -fid $vpd_fid -depth $depth $dump_flags
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

# A global variable representing the file id (fid) of the waves dumped in VPD format.
setDefault vpd_fid 0

# The entry point to enable dumping waves.
#
# If waves are not enabled (i.e. $waves == "none"), we do nothing. If enabled, then first, we run
# the tcl command to establish the dump file. Then, we run `wavedumpScope args...` to enable dumping
# the required hierarchies.
global waves
global simulator
if {$waves ne "none"} {
  set wavedump_db "waves.$waves"
  puts "INFO: Dumping waves in [string toupper $waves] format to $wavedump_db."

  # If waves are enabled, then issue the necessary tcl commands to enable the generation of waves.
  # To explicitly list the hierarchies to dump, use the wavedumpScope proc instead.
  switch $waves {
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
      global vpd_fid
      set vpd_fid [dump -file $wavedump_db -type VPD]
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

  # Decide whether to dump the entire testbench hierarchy by default.
  #
  # If this variable is not set externally, it is set to 1 by default here. When set to 1, it adds
  # the entire top-level testbench instance for dumping waves. For larger designs, this may slow
  # down the simulation. The user can if needed, set it to 0 in the external tcl script that sources
  # this script and manually add the hierarchies of interest in there, using the wavedumpScope proc.
  # See the adjoining sim.tcl for an example.
  setDefault dump_tb_top 1

  if {$dump_tb_top == 1} {
    global tb_top
    wavedumpScope $waves $simulator $tb_top 0
  } else {
    puts "INFO: the hierarchies to be dumped are expected to be indicated externally."
  }
}
