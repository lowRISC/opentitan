# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################################################################
#
# Helper procedure library for waveform capture
#
################################################################################

# A procedure to open a database for waveform dumping
#
# db_name                     Database name
# waves                       The wave-format (fsdb, shm, vpd, vcd, evcd, etc).
# simulator                   The simulator used for running the simulation (vcs, xcelium, etc).
#
proc waveOpenDB {db_name waves simulator} {
  # First, check the waveform file format is compatible with the chosen simulator
  checkWaveformFileCompat $simulator $waves

  switch $waves {
    "fsdb" {
      if {$simulator eq "xcelium"} {
        call fsdbDumpfile $db_name
      } else {
        fsdbDumpfile $db_name
      }
    }

    "shm" {
      database -open $db_name -default -shm
    }

    "vpd" {
      global vpd_fid
      set vpd_fid [dump -file $db_name -type VPD]
    }

    "vcd" {
      if {$simulator eq "xcelium"} {
        database -open $db_name -default -vcd
      }
    }

    "evcd" {
      if {$simulator eq "xcelium"} {
        database -open $db_name -default -evcd
      }
    }

    default {
      puts "ERROR: Unknown wave format: $waves."
      exit
    }
  }
}

# A procedure to enable waveform dumping for a scope in a wave-format agnostic way.
#
# In large designs, dumping waves on the entire hierarchy can significantly slow down the
# simulation. It is useful in that case to only dump the relevant scopes of interest during debug.
#
# waves                          The wave-format (fsdb, shm, vpd, vcd, evcd, etc).
# simulator                      The simulator used for running the simulation (vcs, xcelium, etc).
# scope                          Design / testbench hierarchy level to dump waves. Defaults to $tb_top.
# {depth 0}                      Levels in the hierarchy to dump waves. Defaults to 0 (dump all levels).
# {fsdb_flags "+all"}            Additional string flags passed to fsdbDumpVars (VCS/Xcelium). Defaults to "+all", which
#                                enables dumping of memories, MDAs, structs, unions, power, packed structs, and SVAs.
# {probe_flags "-all"}           Additional string flags passed to probe command (shm/vcd/evcd). Defaults to "-all".
# {dump_flags "-aggregates"}     Additional string flags passed to dump command (VCS-vpd). Defaults to "-aggregates",
#                                which enables dumping of structs and arrays.
proc wavedumpScope {waves simulator scope {depth 0} {fsdb_flags "+all"} {probe_flags "-all"} {dump_flags "-aggregates"}} {
  # First, check the waveform file format is compatible with the chosen simulator
  checkWaveformFileCompat $simulator $waves

  switch $waves {
    "none" {
      puts "INFO: Not dumping from call to wavedumpScope because waves='none'."
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
      if {$depth == 0} {set depth "all"}
      probe "$scope" $probe_flags -depth $depth -memories -shm
    }

    "vpd" {
      global vpd_fid
      dump -add "$scope" -fid $vpd_fid -depth $depth $dump_flags
    }

    "vcd" {
      if {$simulator eq "xcelium"} {
        if {$depth == 0} {set depth "all"}
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
      puts "ERROR: Unknown wave format: $waves."
      exit
    }
  }

  puts "INFO: Dumping waves in scope '$scope:$depth'."
}

# Check simulator compatability with requested waveform file format
proc checkWaveformFileCompat {simulator waves} {
  global checkEq
  switch $waves {
    "fsdb" {
      set supported {"vcs" "xcelium"}
      if {$simulator ni $supported} {
          puts "Waveform format '$waves' is not supported with simulator '$simulator'"
          exit
      }
    }
    "shm" {checkEq simulator "xcelium"}
    "vpd" {checkEq simulator "vcs"}
    "vcd" {checkEq simulator "xcelium"}
    "evcd" {checkEq simulator "xcelium"}
  }
}
