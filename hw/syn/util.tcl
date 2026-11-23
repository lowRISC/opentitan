# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic helpers for SDC/XDC constraint scripts, shared by the top-level SDCs
# and the IP-specific constraint files they source (e.g.
# hw/ip/i3c/syn/i3c_constraints.tcl). Source this file first.
#
# Whenever a pattern in a constraint matches nothing, all tools (Vivado + ASIC)
# silently return an empty collection instead of throwing an error. This then
# leads to downstream errors when those empty collections are handed to
# commands such as create_clock.
# All of this makes sdc debugging notoriously tedious and error-prone.
#
# The procedures below therefore wrap the bare sdc commands into
# `sdc_get_pins`, `sdc_get_cells`, and similar. The calls to these carry a
# human-readable label which gets recorded if the requested pattern does not
# match. On a match, a counter is increased.
# sdc_summary prints both the labels of all commands with no match as well as
# the number of successfully applied commands.

#############################
# Configuration             #
#############################

if {![info exists ::sdc_cfg]} {
  array set ::sdc_cfg {}
}

# Only set a default if the caller has not already chosen a value.
proc sdc_cfg_default {key value} {
  if {![info exists ::sdc_cfg($key)]} {
    set ::sdc_cfg($key) $value
  }
}

## Netlist naming. The tools disagree on this and a wrong spelling matches
## nothing silently, so it is configuration. The defaults are for the
## elaborated netlist in common synthesis tools. Other flows override them.
# Bit of a prim_subreg: the module output pin.
sdc_cfg_default reg_q_pin {q[%d]}
# Bit of the packed pad attribute register, by pad index and field name.
sdc_cfg_default pad_attr_pin {mio_pad_attr_q_reg[%d][%s]/q}

#############################
# Script lookup             #
#############################

# Path of a constraint script, looked for in `sdc/` below the working directory
# first, so a flow that copies the SDCs into a build directory stays
# reproducible, then in each of `dirs`, given as path components relative to
# the working directory. `info script` is not usable for this because
# `read_sdc` does not set it.
proc sdc_find_script {name args} {
  foreach dir [concat [list sdc] $args] {
    set path [file join [pwd] {*}$dir $name]
    if {[file exists $path]} {
      set path [file normalize $path]
      puts "INFO: using ${path}"
      return $path
    }
  }
  # read_sdc swallows a bare `error`, so report it where it will be seen.
  puts "ERROR: cannot find ${name}"
  error "cannot find ${name}"
}

#############################
# Lookups                   #
#############################

# Lookups that found nothing, reported by sdc_summary.
set ::sdc_misses {}
set ::sdc_applied 0

proc sdc_miss {desc pattern} {
  lappend ::sdc_misses "${desc}  (no match: ${pattern})"
}

# get_pins that accounts for a pattern matching nothing. Never filters on
# attributes: the attribute names and the case of their values differ between
# tools, and a bad filter does not return an empty collection but an error that
# some tools then feed into the constraint as a bogus object. Naming the pin
# explicitly through the cfg templates achieves the same selection portably.
proc sdc_get_pins {desc patterns} {
  foreach p $patterns {
    if {[llength [get_pins -quiet $p]] == 0} {
      sdc_miss $desc $p
    }
  }
  return [get_pins -quiet $patterns]
}

proc sdc_get_cells {desc patterns} {
  foreach p $patterns {
    if {[llength [get_cells -quiet $p]] == 0} {
      sdc_miss $desc $p
    }
  }
  return [get_cells -quiet $patterns]
}

# Objects to anchor a `-through` on, tried in order of preference.
#
# A hierarchical module pin is the natural anchor and is what the ASIC flows
# offer, because they constrain an elaborated netlist whose hierarchy is still
# intact. Vivado's FPGA synthesis flattens the design: the module boundary
# pins are gone, but the nets and the leaf cells below the block keep their
# hierarchical names, so the same point in the design is still reachable under
# a different object type. Taking the first kind that matches keeps one set of
# procedures working on both.
#
#   desc   label for sdc_summary
#   specs  list of {pins|nets|cells} {pattern ...} pairs, most preferred first
#
# Once a kind matches, each of its patterns is checked on its own, so that one
# match in a list does not hide the rest.
proc sdc_get_through {desc specs} {
  set tried {}
  foreach {kind patterns} $specs {
    switch -exact -- $kind {
      pins  { set objs [get_pins  -quiet $patterns] }
      nets  { set objs [get_nets  -quiet $patterns] }
      cells { set objs [get_cells -quiet $patterns] }
      default { error "sdc_get_through: unknown object kind '${kind}'" }
    }
    lappend tried $kind
    if {[llength $objs]} {
      set first [lindex $tried 0]
      if {$first ne $kind} {
        puts "INFO: ${desc}: no ${first}, used ${kind} instead"
      }
      foreach p $patterns {
        if {[llength [get_${kind} -quiet $p]] == 0} {
          sdc_miss $desc $p
        }
      }
      return $objs
    }
  }
  sdc_miss $desc "none of [join $tried {, }] matched"
  return {}
}

# Apply set_case_analysis to a pin if it exists, reporting a miss otherwise.
# Returns 1 if applied. Callers may pass `optional` as 1 for cases where a
# miss might legitimately occur and can be tolerated.
proc sdc_case_if_present {value pattern {optional 0}} {
  set pins [get_pins -quiet $pattern]
  if {[llength $pins] == 0} {
    if {!$optional} {
      sdc_miss "set_case_analysis ${value}" $pattern
    }
    return 0
  }
  set_case_analysis $value $pins
  incr ::sdc_applied
  return 1
}

# Pin the output bits of a prim_subreg register to `value`.
proc sdc_case_reg {base width value} {
  for {set bit 0} {$bit < $width} {incr bit} {
    sdc_case_if_present [expr {($value >> $bit) & 1}] \
        "${base}/[format $::sdc_cfg(reg_q_pin) $bit]"
  }
}

# Apply a constraint, reporting rather than aborting when the netlist does not
# have the expected structure.
proc sdc_try {desc script} {
  if {[catch {uplevel 1 $script} err]} {
    lappend ::sdc_misses "${desc}  (error: ${err})"
  }
}

# Report what was applied and what was not since the previous call, prefixed
# with `tag`. A miss is not necessarily fatal (some are expected), but never
# make them silent as it can make sdc debugging very hard.
proc sdc_summary {tag} {
  puts "${tag}: applied ${::sdc_applied} case-analysis constraints"
  if {[llength $::sdc_misses] == 0} {
    puts "${tag}: all lookups matched"
  } else {
    puts "${tag}: WARNING: [llength $::sdc_misses] lookup(s) matched nothing:"
    foreach m $::sdc_misses {
      puts "${tag}:   ${m}"
    }
  }
  set ::sdc_misses {}
  set ::sdc_applied 0
}

#############################
# Pinmux case analysis      #
#############################

# Pin the pinmux selects so that each listed peripheral signal has exactly one
# pad, in both directions, and so no other muxed pad's clock reaches the
# peripheral.
#
#   pinmux       path to the pinmux instance
#   assignments  list of {periph_in_idx periph_out_idx pad_idx}, where
#                periph_out_idx may be `-` for an input-only peripheral signal
#
# Mux encodings (pinmux.sv):
#   mio_mux         = {mio_in, 1'b1, 1'b0}        -> insel  = pad_idx + 2
#   periph_data_mux = {periph_to_mio_i, 0, 1, 0}  -> outsel = periph_out + 3
proc sdc_pinmux_case_analysis {pinmux assignments} {
  set pads {}
  foreach entry $assignments {
    lassign $entry periph_in periph_out pad
    lappend pads $pad

    # Input: the peripheral input reads this pad.
    sdc_case_reg "${pinmux}/u_reg/u_mio_periph_insel_${periph_in}" 6 [expr {$pad + 2}]
    # Output: this pad is driven by the peripheral output, where there is one.
    if {$periph_out ne "-"} {
      sdc_case_reg "${pinmux}/u_reg/u_mio_outsel_${pad}" 7 [expr {$periph_out + 3}]
    }
  }

  foreach pad [lsort -unique -integer $pads] {
    # Set the bit corresponding to $pad in the SLEEP_STATUS CSR to 0. This
    # is the active setting which forwards the selected peripheral output to
    # the pad, and not its sleep retention value (CSRs are 32 bit wide).
    set sleep_reg [expr {$pad < 32 ? "u_mio_pad_sleep_status_0_en_${pad}"
                                   : "u_mio_pad_sleep_status_1_en_${pad}"}]
    sdc_case_if_present 0 \
        "${pinmux}/u_reg/${sleep_reg}/[format $::sdc_cfg(reg_q_pin) 0]"

    # Pad attributes that would otherwise make the pad non-unate or cut the
    # signal (prim_pad_wrapper.sv):
    #   invert        XORs both the input and the output
    #   virt_od_en    makes the output enable depend on the output data
    #   input_disable turns the input buffer off
    # Which of these exist depends on the technology's WARL mask, so a missing
    # one is reported but not treated as an error.
    set applied {}
    foreach attr {invert virt_od_en input_disable} {
      if {[sdc_case_if_present 0 \
               "${pinmux}/[format $::sdc_cfg(pad_attr_pin) $pad $attr]" 1]} {
        lappend applied $attr
      }
    }
    if {[llength $applied] == 0} {
      sdc_miss "MIO pad ${pad} attributes" \
          "${pinmux}/[format $::sdc_cfg(pad_attr_pin) $pad invert]"
    }
    puts "INFO: MIO pad ${pad} attributes pinned: [join $applied { }]"
  }
}
