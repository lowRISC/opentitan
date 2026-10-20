# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# I3C timing constraints, shared by the ASIC (SDC) and the FPGA (XDC) flows.
#
# The I3C IP shares one SCL/SDA pad pair for Controller and Target roles:
#
#  - The Controller is synchronous to clk_i and *generates* SCL. With
#    HalfCycleScl set, SCL is `state_q[ST_SCL] | gen_hc_scl.scl_n`, i.e., a
#    posedge flop OR'ed with a negedge flop (i3c_controller_trx.sv).
#  - The Target has no free-running clock. It is clocked by the bus itself:
#    SCL and its inverse for SDR/HDR-DDR data, SDA and its inverse for
#    START/STOP detection (i3c_input_buffers.sv, four clock trees).
#
# Each pad therefore carries two mutually exclusive SCL *sources*: One from our
# Controller, and one from an external Active Controller; the Target is timed
# against the external one.
# The generated SCL still reaches the Target clock trees, because it leaves and
# re-enters the chip through the pad. The paths it clocks there are cut, as the
# resulting skews would make timing closure impossible (see i3c_create_clocks).
#
# Timing is per MIPI I3C Basic v1.2 (+ Errata 01), Tables 48-50 and Figures
# 73/80/81. In SDR the Target launches SDA on the falling SCL edge and samples
# on the rising edge, but both of its shift registers sample unconditionally and
# the output enable toggles on both edges, so both edges are referenced even in
# pure SDR; HDR-DDR adds data on both edges.
#
# Usage:
#   set ::i3c_cfg(reg_q_pin) {q_reg[%d]/Q} ;# netlist naming; defaults are ASIC
#   set ::i3c_cfg(board_dly_max) 2.0       ;# override any default below
#   source .../i3c_constraints.tcl
#   i3c_pinmux_case_analysis $u_pinmux { {38 38 19} {39 39 18} ... }
#   i3c_constrain $inst IOB10 IOB9 I3C0 $clk_pin $clk_name $clk_period
#   i3c_constrain_rstdet $rstdet_inst I3C0 $clk_name
#   i3c_summary
#
# and, in the check-only flow that times the domain crossings:
#   i3c_set_cdc_bounds $inst I3C0 $clk_name $clk_period
#   i3c_set_rstdet_cdc_bounds $rstdet_inst I3C0 $aon_period
#   i3c_summary
#
# All delay values are in nanoseconds.
#
# Note: Whenever a pattern in the commands below matches nothing, all tools
# (Vivado + ASIC) silently return an empty collection instead of throwing an
# error. This then leads to downstream errors when those empty collections are
# handed to commands such as create_clock.
# All of this makes sdc debugging notoriously tedious and error-prone.
#
# This file therefore wraps the bare sdc commands into `i3c_get_pins`,
# `i3c_get_cells`, and similar. The calls to these carry a human-readable label
# which gets recorded if the requested pattern does not match. On a match, a
# counter is increased.
# i3c_summary then prints both the labels of all commands with no match as well
# as the number of successfully applied commands.

#############################
# Configuration             #
#############################

if {![info exists ::i3c_cfg]} {
  array set ::i3c_cfg {}
}

# Only set a default if the caller has not already chosen a value.
proc i3c_cfg_default {key value} {
  if {![info exists ::i3c_cfg($key)]} {
    set ::i3c_cfg($key) $value
  }
}

## Bus timing, from the I3C Basic v1.2 specification.
# Table 50: fSCL max 12.9 MHz. This bounds an externally driven SCL; our own
# Controller's SCL is derived from clk_i instead (see i3c_create_clocks).
i3c_cfg_default scl_ext_period 77.5
# Table 50: tDIG_L and tDIG_H, the SCL low and high periods, min 32 ns each.
# Note 2 allows an extreme 40/60 duty cycle, so a half SCL period can be shorter
# than half of scl_ext_period.
i3c_cfg_default tdig_min 32.0
# Table 50: tSCO, SCL in to SDA out for a Target, max 20 ns. This is our own
# obligation when acting as a Target.
i3c_cfg_default tsco_max 20.0
# What a remote Target may take before it presents read data. Devices slower
# than 20 ns must advertise it in the BCR (Table 50 note 7), so 20 ns is the
# compliant bound. Figure 73 counts only the Target's input pad and internal
# delay (t4 + t5) as tSCO; the wiring both ways (t3, t7) comes on top.
i3c_cfg_default tsco_ext_max 20.0
# Table 50: tSU_PP / Table 49: tSU_OD, SDA setup, min 3 ns.
i3c_cfg_default tsu_pp 3.0
# Table 50: tHD_PP, min 0 for a Target, tCR/tCF + 3 ns for a Controller.
i3c_cfg_default thd_pp_tgt 0.0
# Table 50 note 5 caps tCR/tCF at 60 ns; integration_notes.md requires <= 8 ns
# to reach the full 12.5 MHz signalling rate.
i3c_cfg_default tcr 8.0
i3c_cfg_default tcf 8.0

## Whether to model the I3C bus I/O timing at all. With this off, only the bus
## clocks, the pinmux case analysis and the internal budgets are applied: the
## logic is still timed, but the interface is not held to the specification.
## Turn it off for a target that physically cannot meet the specification and
## is only used for functional bring-up.
## TODO: This is currently true for CW340 due to SDA and SCL going through
## pinmux. Ensure bus delays work once the sparse pinmux lands.
i3c_cfg_default bus_io_delays 1

## Board and pad delays. Set these to the real numbers for the system.
# Pad-to-pad wiring (t3 and t7 of specification Figure 73).
i3c_cfg_default board_dly_max 2.0
i3c_cfg_default board_dly_min 0.1
# Extra budget for our own pad cells, for flows where the pad is a black box
# without timing. Leave at 0 when STA already models the pad, which is the
# normal case for both a foundry pad library and an FPGA IOBUF.
i3c_cfg_default pad_out_dly_max 0.0
i3c_cfg_default pad_out_dly_min 0.0
i3c_cfg_default pad_in_dly_max 0.0
i3c_cfg_default pad_in_dly_min 0.0

## Controller SCL waveform, in edges of the clk_i source clock.
# i3c_timing_pkg::tm_params() turns the target SCL period (TPERIOD_SDR0 = 80 ns)
# and high interval (TDIGH = 36 ns) into clk_i cycle counts. At ClkFreq = 96 MHz
# this yields tchh=2, tchs=1, hcext=1, tclh=3, tcls=2 (the package stores them
# pre-decremented for down-counting). SCL is high for tchh+tchs = 3 cycles and
# the half-cycle extension holds it high half a cycle longer, so the period is
# 8 cycles with a 3.5 cycle high phase and a 4.5 cycle low phase.
# Counting source clock transitions, edge 1 is the first rising edge, edge 8 the
# falling edge 3.5 cycles later and edge 17 the rising edge 8 cycles later.
# Software can slow SCL down through the CTRL_TIME_* registers; this models the
# fastest case, which is the one that has to close.
i3c_cfg_default scl_edges {1 8 17}

## Where the Controller samples SDA, in clk_i cycles, for each of its capture
## points. The Controller samples with clk_i, so each capture point needs a
## multicycle that matches the state it is captured in
## (i3c_controller_trx.sv): Without one, STA pairs the SCL edge with the nearest
## clk_i edge and reports violations the design cannot meet.
# Read data, end of State_ClkLoAwaitD: the clk_i edge on which SCL rises again.
# Arbitration and IBI, captured in State_ArbClkHiHoldD, are launched by the same
# falling edge but captured later, so this also covers them.
i3c_cfg_default ctrl_rx_cycles 5
# HDR-DDR even bits, end of State_ClkHiAwaitD, launched by the rising edge.
i3c_cfg_default ctrl_rx_ddr_cycles 3
# SDR read T-bit, end of State_ClkLoSampleD, earlier than the read data.
i3c_cfg_default ctrl_tbit_cycles 3
# The Controller drives SDA tcls cycles ahead of the SCL edge that the far end
# samples on, so the launch edge is earlier than the one STA would pick.
i3c_cfg_default ctrl_tx_cycles 2
# The first SDA change after an SCL edge, counted for the hold check. SDA next
# moves tchh = 2 cycles after SCL rises (HDR-DDR, T-bit drive) and 2.5 cycles
# after it falls (end of State_ClkLoHoldD), i.e. 4 cycles after the setup launch
# in both cases. The handovers on the rising edge itself (ACK, T-bit) keep the
# SDA level, so they do not count.
i3c_cfg_default ctrl_tx_hold_cycles 3

## Internal paths.
# Budget for clk_i <-> bus clock domain crossings, as a fraction of the clk_i
# period. Only applied by i3c_set_cdc_bounds, which belongs in the check-only
# flow: in the synthesis SDC the asynchronous clock groups would override it.
i3c_cfg_default cdc_fraction 0.9
# Window the START/STOP detectors have to resolve a bus condition in. SDA and
# SCL are asynchronous to each other, so these clock-as-data paths get an
# explicit bound rather than a clock relationship. Table 49: tCAS min 38.4 ns,
# tCBP min tCAS/2; Table 50: tCASr and tCBSr min tCAS/2.
i3c_cfg_default start_stop_max 19.2
# Window the HDR Exit and Restart detector has to resolve each edge of its
# pattern in. Section 4.3.10.2: each transition on SDA and/or SCL is separated
# by at least tDIG_H.
i3c_cfg_default hdr_patt_max 32.0

## Netlist naming. The tools disagree on all of this and a wrong spelling
## matches nothing silently, so it is configuration. The defaults are for the
## Cadence/Synopsys ASIC flows; the FPGA flow overrides them.
# Bit of a prim_subreg: the module output pin.
i3c_cfg_default reg_q_pin {q[%d]}
# Bit of the packed pad attribute register, by pad index and field name.
i3c_cfg_default pad_attr_pin {mio_pad_attr_q_reg[%d][%s]/q}
# Buffer pins. A clock has to be created on a pin, stopping a clock takes pins,
# and a buffer is not a sequential cell so it is not a valid path startpoint
# either, which is why its output is named here as well.
i3c_cfg_default buf_in_pin A
i3c_cfg_default buf_out_pin Y
# Path from a prim_flop_2sync instance down to its first-stage flop cells.
# These do not follow the `_reg` convention that inferred flops do.
i3c_cfg_default sync_flop {u_sync_1/*flop*}

# Timing exceptions accept sequential cells as well as pins, and a cell has the
# same name in every tool while its pins do not (d/D, q/Q, Y/O), so flops are
# selected as cells below. The patterns are qualified with `_reg` because an
# unqualified wildcard also picks up the tool-generated muxes that share the
# signal name, which are not valid path endpoints.
# Annoyingly, one invalid object often aborts the whole constraint call,
# and not as a catchable Tcl error.

#############################
# Helpers                   #
#############################

# Lookups that found nothing, reported by i3c_summary.
set ::i3c_misses {}
set ::i3c_applied 0

proc i3c_miss {desc pattern} {
  lappend ::i3c_misses "${desc}  (no match: ${pattern})"
}

# get_pins that accounts for a pattern matching nothing. Never filters on
# attributes: the attribute names and the case of their values differ between
# tools, and a bad filter does not return an empty collection but an error that
# some tools then feed into the constraint as a bogus object. Naming the pin
# explicitly through the cfg templates achieves the same selection portably.
proc i3c_get_pins {desc pattern} {
  set pins [get_pins -quiet $pattern]
  if {[llength $pins] == 0} {
    i3c_miss $desc $pattern
  }
  return $pins
}

proc i3c_get_cells {desc pattern} {
  set cells [get_cells -quiet $pattern]
  if {[llength $cells] == 0} {
    i3c_miss $desc $pattern
  }
  return $cells
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
#   desc   label for i3c_summary
#   specs  list of {pins|nets|cells} {pattern ...} pairs, most preferred first
proc i3c_get_through {desc specs} {
  set tried {}
  foreach {kind patterns} $specs {
    switch -exact -- $kind {
      pins  { set objs [get_pins  -quiet $patterns] }
      nets  { set objs [get_nets  -quiet $patterns] }
      cells { set objs [get_cells -quiet $patterns] }
      default { error "i3c_get_through: unknown object kind '${kind}'" }
    }
    lappend tried $kind
    if {[llength $objs]} {
      set first [lindex $tried 0]
      if {$first ne $kind} {
        puts "i3c_constraints: ${desc}: no ${first}, used ${kind} instead"
      }
      return $objs
    }
  }
  i3c_miss $desc "none of [join $tried {, }] matched"
  return {}
}

# Apply set_case_analysis to a pin if it exists, reporting a miss otherwise.
# Returns 1 if applied. Some attribute bits are legitimately absent because the
# technology's WARL mask removes them, so callers that expect that pass
# `optional`.
proc i3c_case_if_present {value pattern {optional 0}} {
  set pins [get_pins -quiet $pattern]
  if {[llength $pins] == 0} {
    if {!$optional} {
      i3c_miss "set_case_analysis ${value}" $pattern
    }
    return 0
  }
  set_case_analysis $value $pins
  incr ::i3c_applied
  return 1
}

proc i3c_case_reg {base width value} {
  for {set bit 0} {$bit < $width} {incr bit} {
    i3c_case_if_present [expr {($value >> $bit) & 1}] \
        "${base}/[format $::i3c_cfg(reg_q_pin) $bit]"
  }
}

# Apply a constraint, reporting rather than aborting when the netlist does not
# have the expected structure.
proc i3c_try {desc script} {
  if {[catch {uplevel 1 $script} err]} {
    lappend ::i3c_misses "${desc}  (error: ${err})"
  }
}

# Report what was applied and what was not. Call once after the i3c_constrain
# calls. A miss is not fatal on its own - some are expected - but it is never
# silent, which can make sdc debugging very hard.
proc i3c_summary {} {
  puts "i3c_constraints: applied ${::i3c_applied} case-analysis constraints"
  if {[llength $::i3c_misses] == 0} {
    puts "i3c_constraints: all lookups matched"
    return
  }
  puts "i3c_constraints: WARNING: [llength $::i3c_misses] lookup(s) matched nothing:"
  foreach m $::i3c_misses {
    puts "i3c_constraints:   ${m}"
  }
}

#############################
# Pinmux case analysis      #
#############################

# Pin the pinmux selects so that each I3C signal has exactly one pad, in both
# directions, and so no other muxed pad's clock reaches the I3C clock trees.
# This is independent of where the I3C instances sit in the hierarchy.
#
#   pinmux       path to the pinmux instance
#   assignments  list of {periph_in_idx periph_out_idx pad_idx}, where
#                periph_out_idx may be `-` for an input-only peripheral such as
#                the reset detector's SCL/SDA observation inputs.
#
# Mux encodings (pinmux.sv):
#   mio_mux         = {mio_in, 1'b1, 1'b0}        -> insel  = pad_idx + 2
#   periph_data_mux = {periph_to_mio_i, 0, 1, 0}  -> outsel = periph_out + 3
proc i3c_pinmux_case_analysis {pinmux assignments} {
  set pads {}
  foreach entry $assignments {
    lassign $entry periph_in periph_out pad
    lappend pads $pad

    # Input: the peripheral input reads this pad.
    i3c_case_reg "${pinmux}/u_reg/u_mio_periph_insel_${periph_in}" 6 [expr {$pad + 2}]
    # Output: this pad is driven by the peripheral output, where there is one.
    if {$periph_out ne "-"} {
      i3c_case_reg "${pinmux}/u_reg/u_mio_outsel_${pad}" 7 [expr {$periph_out + 3}]
    }
  }

  foreach pad [lsort -unique -integer $pads] {
    # Take the functional branch of the sleep retention mux in front of the
    # output select (pinmux.sv).
    set sleep_reg [expr {$pad < 32 ? "u_mio_pad_sleep_status_0_en_${pad}"
                                   : "u_mio_pad_sleep_status_1_en_${pad}"}]
    i3c_case_if_present 0 \
        "${pinmux}/u_reg/${sleep_reg}/[format $::i3c_cfg(reg_q_pin) 0]"

    # Pad attributes that would otherwise make the pad non-unate or cut the
    # signal (prim_pad_wrapper.sv):
    #   invert        XORs both the input and the output
    #   virt_od_en    makes the output enable depend on the output data
    #   input_disable turns the input buffer off
    # Which of these exist depends on the technology's WARL mask, so a missing
    # one is reported but not treated as an error.
    set applied {}
    foreach attr {invert virt_od_en input_disable} {
      if {[i3c_case_if_present 0 \
               "${pinmux}/[format $::i3c_cfg(pad_attr_pin) $pad $attr]" 1]} {
        lappend applied $attr
      }
    }
    if {[llength $applied] == 0} {
      i3c_miss "MIO pad ${pad} attributes" \
          "${pinmux}/[format $::i3c_cfg(pad_attr_pin) $pad invert]"
    }
    puts "i3c_constraints: MIO pad ${pad} attributes pinned: [join $applied { }]"
  }
}

#############################
# Clocks                    #
#############################

# Inputs of the true and the inverted SDA clock buffer of one i3c_input_buffers
# instance, as one collection. Each is looked up on its own first, so that a
# missing one is reported even when the other matches.
proc i3c_sda_clock_pins {desc inbufs} {
  set patterns {}
  foreach buf {u_sda0_clk u_sda0_clk_n} {
    set pattern ${inbufs}/${buf}/u_buf/*/$::i3c_cfg(buf_in_pin)
    if {[llength [i3c_get_pins "${desc} SDA clock input of ${buf}" $pattern]]} {
      lappend patterns $pattern
    }
  }
  if {[llength $patterns] == 0} {
    return {}
  }
  return [get_pins -quiet $patterns]
}

# Objects that every crossing between clk_i and the bus-clocked logic of the
# primary partition passes through, and that the Controller's own paths to and
# from the pads do not:
#   u_targ_trx, u_patt_det  every clk_i input and every status output of the
#                           blocks clocked by SCL and SDA
#   u_sync_ctrl, u_sync_targ  SCL and SDA sampled as data by clk_i
#   i3c_sync_data (to SCL)  the clk_i toggle, data and reset into the SCL side,
#                           and the acknowledge back into clk_i
# The data synchronized out of the transceiver already passes u_targ_trx.
#
# The module boundary pins say this most precisely, but they only exist while
# the hierarchy does. Where it has been flattened, the leaf cells of the same
# blocks are the fallback: a crossing that ends at one of those flops passes
# through it just the same (see i3c_get_through).
proc i3c_bus_crossing_pins {inst} {
  set core ${inst}/u_core
  set blocks [list \
      ${core}/u_targ_trx \
      ${core}/u_patt_det \
      ${core}/u_sync_ctrl \
      ${core}/u_sync_targ]
  foreach sync {
    u_targ_txc_sync
    u_arb_sync
    gen_targ_txd_sync[*].u_targ_txd_sync
  } {
    lappend blocks \
        ${core}/u_target/${sync} \
        ${core}/u_target/${sync}/gen_src_toggle.u_sync_tgl_ack
  }

  # Only the data input of the two bus observers is a crossing; their clock and
  # reset are not. The blocks above have no such distinction.
  set pin_patterns {}
  foreach blk $blocks {
    if {[string match */u_sync_ctrl $blk] ||
        [string match */u_sync_targ $blk] ||
        [string match */u_sync_tgl_ack $blk]} {
      lappend pin_patterns ${blk}/d_i*
    } else {
      lappend pin_patterns ${blk}/*
    }
  }
  set cell_patterns {}
  foreach blk $blocks {
    lappend cell_patterns ${blk}/*
  }

  return [i3c_get_through "${inst} bus crossings" \
      [list pins $pin_patterns cells $cell_patterns]]
}

# Create the bus clocks for one I3C instance.
#
#   inst       path to the i3c primary partition instance
#   scl_port   chip port carrying SCL
#   sda_port   chip port carrying SDA
#   prefix     clock name prefix, e.g. I3C0
#   clk_pin    pin carrying the IP's clk_i, used as the generated clock source
#   clk_name   name of the clock on clk_pin, used as the master clock
proc i3c_create_clocks {inst scl_port sda_port prefix clk_pin clk_name} {
  set inbufs ${inst}/u_core/u_targ_inbufs

  # An external Active Controller drives SCL; we are a Target. 12.9 MHz is the
  # Table 50 maximum, including the short bursts caused by jitter and skew.
  create_clock -name ${prefix}_SCL_EXT -period $::i3c_cfg(scl_ext_period) \
      [get_ports $scl_port] -add

  # The clock above has a 50% duty cycle, but either half of the SCL period may
  # be as short as tDIG_min. Charge the difference to the transfers between the
  # two edges only; paths between like edges keep the whole period. Table 50
  # does not expect the fastest clock and the worst duty cycle at the same time,
  # so this is conservative.
  set dc_loss [expr {$::i3c_cfg(scl_ext_period) / 2.0 - $::i3c_cfg(tdig_min)}]
  if {$dc_loss > 0} {
    set scl_ext [get_clocks ${prefix}_SCL_EXT]
    set_clock_uncertainty -setup $dc_loss -rise_from $scl_ext -fall_to $scl_ext
    set_clock_uncertainty -setup $dc_loss -fall_from $scl_ext -rise_to $scl_ext
  }

  # SDA clocks the Target's START/STOP and HDR pattern detectors
  # (i3c_target_trx.sv, i3c_patt_detector.sv). It is declared on the inputs of
  # its clock buffers rather than on the pad, because SDA is only a clock inside
  # the Target, and because a port that carries a clock cannot also take the
  # input delays that SDA needs as data. The true and the inverted buffer are
  # separate cells fed from the same net, so a clock declared on one does not
  # reach the other; both are sources of the same clock.
  set sda_clk_pins [i3c_sda_clock_pins "${prefix}" $inbufs]
  if {[llength $sda_clk_pins]} {
    create_clock -name ${prefix}_SDA -period $::i3c_cfg(scl_ext_period) \
        $sda_clk_pins -add
    set_clock_groups -name ${prefix}_SDA_ASYNC -asynchronous \
        -group [get_clocks ${prefix}_SDA]
  }

  # Our own Controller drives SCL, derived from clk_i. Only one of the two can
  # be driving the pad, so they are physically exclusive. This clock exists to
  # give the Controller's own SDA timing a reference, so it is only needed when
  # the bus I/O timing is modelled.
  if {$::i3c_cfg(bus_io_delays)} {
    create_generated_clock -name ${prefix}_SCL_INT -source [get_pins $clk_pin] \
        -edges $::i3c_cfg(scl_edges) -master_clock [get_clocks $clk_name] \
        [get_ports $scl_port] -add

    set_clock_groups -name ${prefix}_SCL_SRC -physically_exclusive \
        -group [get_clocks ${prefix}_SCL_EXT] \
        -group [get_clocks ${prefix}_SCL_INT]

    # Our own SCL leaves and re-enters the chip through the pad, so whenever
    # the Controller drives the bus, the Target is clocked by a copy of clk_i
    # that has made a full pad-board-pad round trip. STA relates the two and
    # charges the round trip as skew, which breaks setup and hold at the same
    # time. Stopping the clock at the Target buffer inputs does not prevent
    # this: `set_sense -stop_propagation` is accepted but the paths remain.
    # Instead, cut the paths on which SCL_INT clocks the Target side. These are
    # the same synchronized crossings that the asynchronous SCL_EXT group cuts
    # for an external Controller.
    #
    # The cut has to name SCL_INT on the bus side. Cutting between clk_i and
    # the bus-clocked cells would also remove their real SCL_EXT and SDA
    # crossings, and a false path outranks the set_max_delay that bounds those
    # in the check-only flow (i3c_set_cdc_bounds). The Controller's own paths
    # to and from the SDA port also relate clk_i and SCL_INT, so the crossings
    # are selected by the hierarchical pins they pass through instead.
    i3c_try "cut the ${prefix} SCL loopback" {
      set scl_int [get_clocks ${prefix}_SCL_INT]
      # Target flops clocked by our own SCL, among themselves and against the
      # SDA port. The I/O delays on SCL_INT describe our Controller talking to
      # a remote Target, not our Target.
      set_false_path -from $scl_int -to $scl_int

      # The Target's SDA-clocked logic against the same loopback. The two bus
      # clocks are related here only because both are derived from our own
      # clk_i while we drive the bus, which is precisely the round trip being
      # cut. The SCL_EXT copies of these paths stay timed, and they are the
      # ones that matter; when we drive SCL, our own Target is held disabled.
      set sda [get_clocks -quiet ${prefix}_SDA]
      if {[llength $sda]} {
        set_false_path -from $sda -to $scl_int
        set_false_path -from $scl_int -to $sda
      }

      # Our own clk_i against the loopback. Naming the clocks alone would also
      # cut the Controller's own paths to and from the SDA port, which are
      # timed against SCL_INT on purpose, so these are narrowed to the
      # hierarchical pins the Target-side crossings pass through.
      set xing [i3c_bus_crossing_pins $inst]
      if {[llength $xing]} {
        set_false_path -from [get_clocks $clk_name] -to $scl_int -through $xing
        set_false_path -from $scl_int -to [get_clocks $clk_name] -through $xing
      }
    }
  }

  # A bus driven from outside has no relationship to anything else in the
  # design. A single-clock group is asynchronous to every other clock.
  #
  # SCL_INT is deliberately NOT grouped here: it is generated from clk_i and
  # must stay related to it, otherwise the Controller's own output and input
  # paths would be cut. The caller has to add it to the group that holds clk_i
  # (see i3c_scl_int_clock).
  set_clock_groups -name ${prefix}_SCL_EXT_ASYNC -asynchronous \
      -group [get_clocks ${prefix}_SCL_EXT]
}

# Name of the generated clock that has to join the clk_i clock group at top
# level, or an empty string when the bus I/O timing is not modelled and the
# clock was therefore never created.
proc i3c_scl_int_clock {prefix} {
  if {!$::i3c_cfg(bus_io_delays)} {
    return ""
  }
  return ${prefix}_SCL_INT
}

#############################
# I/O delays                #
#############################

# Constrain SDA against SCL for one I3C instance, in both roles and on both
# clock edges. The reference point is the chip port, which is where the
# specification defines its timing.
proc i3c_set_io_delays {inst scl_port sda_port prefix clk_name} {
  if {!$::i3c_cfg(bus_io_delays)} {
    puts "i3c_constraints: ${prefix}: bus I/O timing not modelled"
    return
  }
  set sda [get_ports $sda_port]

  ## Target role: the bus is driven by an external Active Controller, so the
  ## timing is relative to SCL_EXT.
  set scl_clk ${prefix}_SCL_EXT
  # Distance to the opposite SCL edge. i3c_create_clocks shortens the transfers
  # between the two edges to tDIG_min with clock uncertainty, so it has to be
  # the same number here for the half period to cancel out below.
  set half $::i3c_cfg(tdig_min)

  # Output. Our tSCO obligation is measured from the SCL edge at the pad, so
  # the required time has to land tSCO after that edge. With the capture edge
  # half a period away, that is an output delay of (half period - tSCO).
  set tgt_out_max [expr {$half - $::i3c_cfg(tsco_max) \
                         + $::i3c_cfg(pad_out_dly_max)}]

  # Hold. SDA may not change until tHD_PP after the capture edge. Figure 81 is
  # the Target *out* timing, so like tSCO this is referenced at our own pads.
  # As a requirement after the edge, tHD_PP enters the minimum output delay
  # negated. Note that tHD_PP is 0 for a Target, so this usually equates to 0.
  set tgt_out_min [expr {0.0 - $::i3c_cfg(thd_pp_tgt)}]

  # Input. A remote Controller presents SDA tSU_PP before the edge that
  # samples it and holds it tHD_PP = tCF/tCR + 3 ns afterwards. Setup and hold
  # are properties of the receiver, which is us, so tSU_PP is already a
  # guarantee at our own pads.
  set tgt_in_max [expr {$half - $::i3c_cfg(tsu_pp) \
                        + $::i3c_cfg(pad_in_dly_max)}]

  # The hold guarantee is referenced at the remote Controller's pads (Figure
  # 80 is its *out* timing), not at ours.
  set tgt_in_min_f [expr {$::i3c_cfg(tcf) + 3.0}]
  set tgt_in_min_r [expr {$::i3c_cfg(tcr) + 3.0}]

  # Both Target shift registers sample SDA on every edge and the output enable
  # select toggles on both edges, so both references are needed even in SDR.
  set_output_delay -max $tgt_out_max -clock $scl_clk             $sda -add_delay
  set_output_delay -min $tgt_out_min -clock $scl_clk             $sda -add_delay
  set_output_delay -max $tgt_out_max -clock $scl_clk -clock_fall $sda -add_delay
  set_output_delay -min $tgt_out_min -clock $scl_clk -clock_fall $sda -add_delay

  set_input_delay -max $tgt_in_max   -clock $scl_clk             $sda -add_delay
  set_input_delay -min $tgt_in_min_r -clock $scl_clk             $sda -add_delay
  set_input_delay -max $tgt_in_max   -clock $scl_clk -clock_fall $sda -add_delay
  set_input_delay -min $tgt_in_min_f -clock $scl_clk -clock_fall $sda -add_delay

  ## Controller role. SDA is launched and captured by clk_i, but the bus timing
  ## is relative to the SCL we generate, so SCL_INT is the reference.
  set scl_clk ${prefix}_SCL_INT

  # Output: SDA must be stable tSU_PP before the capturing edge and must not
  # change until tHD_PP after it, so the hold number is negative.
  set ctrl_out_max   [expr {$::i3c_cfg(tsu_pp) + $::i3c_cfg(pad_out_dly_max)}]
  set ctrl_out_min_f [expr {0.0 - ($::i3c_cfg(tcf) + 3.0)}]
  set ctrl_out_min_r [expr {0.0 - ($::i3c_cfg(tcr) + 3.0)}]

  set_output_delay -max $ctrl_out_max   -clock $scl_clk             $sda -add_delay
  set_output_delay -min $ctrl_out_min_r -clock $scl_clk             $sda -add_delay
  set_output_delay -max $ctrl_out_max   -clock $scl_clk -clock_fall $sda -add_delay
  set_output_delay -min $ctrl_out_min_f -clock $scl_clk -clock_fall $sda -add_delay

  # The RTL moves SDA a whole tcls ahead of the edge the far end samples on,
  # whereas STA would launch from the last clk_i edge before that edge. For the
  # hold check, the next change comes several cycles after that edge rather
  # than on the clk_i edge that moves SCL (see ctrl_tx_hold_cycles).
  set tx $::i3c_cfg(ctrl_tx_cycles)
  set_multicycle_path -setup $tx -start -from [get_clocks $clk_name] \
      -to [get_clocks $scl_clk] -through $sda
  set_multicycle_path -hold $::i3c_cfg(ctrl_tx_hold_cycles) -start \
      -from [get_clocks $clk_name] -to [get_clocks $scl_clk] -through $sda

  # Input: a remote Target answers at most tSCO after the SCL edge reaches it,
  # and the answer then has to travel back.
  #
  # This is the one place where board delays belong, because it is the only one
  # where the two ends measure from different points. Everywhere else both
  # parameters of a check sit at the same device's pads and the flight cancels
  # between SCL and SDA, apart from board skew considerations.
  # Here tSCO is referenced at the remote Target's pad (Figure 81) while our
  # reference is our own port, and the two differ by the outbound flight, so the
  # wiring counts twice: t3 for SCL out, t7 (with our pad) for SDA back.
  #
  # Both edges launch data: the falling edge for SDR and the odd HDR-DDR bits,
  # the rising edge for the even HDR-DDR bits.
  set ctrl_in_max [expr {$::i3c_cfg(tsco_ext_max) + $::i3c_cfg(pad_in_dly_max) + \
                         2 * $::i3c_cfg(board_dly_max)}]
  set ctrl_in_min [expr {$::i3c_cfg(thd_pp_tgt) + $::i3c_cfg(pad_in_dly_min) + \
                         2 * $::i3c_cfg(board_dly_min)}]

  set_input_delay -max $ctrl_in_max -clock $scl_clk             $sda -add_delay
  set_input_delay -min $ctrl_in_min -clock $scl_clk             $sda -add_delay
  set_input_delay -max $ctrl_in_max -clock $scl_clk -clock_fall $sda -add_delay
  set_input_delay -min $ctrl_in_min -clock $scl_clk -clock_fall $sda -add_delay

  # The Controller samples with clk_i, not with SCL, and `rx_advance`
  # (i3c_controller_trx.sv) captures SDA in four different states. Each sits a
  # different number of clk_i cycles after the SCL edge that launched the data,
  # so one blanket multicycle would only be correct for the read data and too
  # loose for the rest.
  #
  # Three of the four are covered by edge: everything launched by the falling
  # edge, and everything launched by the rising edge. Arbitration and IBI are
  # open-drain SDR phases, so they are launched by the falling edge as well and
  # captured later than the read data, which leaves the blanket conservative.
  # The T-bit is captured earlier than its edge-mate, so it gets an exception
  # of its own, aimed at the endpoint; a `-to <cell>` exception is more
  # specific than a `-to <clock>` one and takes precedence.
  #
  #   state                launch       capture   cycles
  #   State_ClkLoAwaitD    fall 3.5T    8T        ctrl_rx_cycles
  #   State_ClkHiAwaitD    rise 0       3T        ctrl_rx_ddr_cycles
  #   State_ClkLoSampleD   fall 3.5T    6T        ctrl_tbit_cycles
  #   State_ArbClkHiHoldD  fall 3.5T    9T, 10T   (ctrl_rx_cycles)
  #
  # The capture instants come from the state durations: `cnt` is loaded from
  # phase_cycles(state_q) on leaving a state, so each state lasts the *previous*
  # state's parameter.
  set rx $::i3c_cfg(ctrl_rx_cycles)
  set_multicycle_path -setup $rx -end -fall_from [get_clocks $scl_clk] \
      -to [get_clocks $clk_name] -through $sda
  set_multicycle_path -hold [expr {$rx - 1}] -end -fall_from [get_clocks $scl_clk] \
      -to [get_clocks $clk_name] -through $sda

  # HDR-DDR even bits, captured at the end of State_ClkHiAwaitD, i.e. while SCL
  # is still high, which is only 3.5 cycles long.
  set ddr $::i3c_cfg(ctrl_rx_ddr_cycles)
  set_multicycle_path -setup $ddr -end -rise_from [get_clocks $scl_clk] \
      -to [get_clocks $clk_name] -through $sda
  set_multicycle_path -hold [expr {$ddr - 1}] -end -rise_from [get_clocks $scl_clk] \
      -to [get_clocks $clk_name] -through $sda

  # The SDR read T-bit is captured earlier than the read data, at the end of
  # State_ClkLoSampleD, so the blanket read-data multicycle would let it arrive
  # two cycles late.
  set tbit [i3c_get_cells "${prefix} SDR T-bit sample" \
      ${inst}/u_core/u_ctrl_trx/sdr_tbit_targ_q_reg*]
  if {[llength $tbit]} {
    set tb $::i3c_cfg(ctrl_tbit_cycles)
    set_multicycle_path -setup $tb -end -fall_from [get_clocks $scl_clk] \
        -to $tbit
    set_multicycle_path -hold [expr {$tb - 1}] -end -fall_from [get_clocks $scl_clk] \
        -to $tbit
  }

  # Arbitration and IBI are captured in State_ArbClkHiHoldD, while SCL is high.
  # Nothing drives SDA on the rising edge in these phases, so pairing them with
  # it would only charge a remote tSCO that does not occur there.
  set arb [i3c_get_cells "${prefix} arbitration sample" \
      ${inst}/u_core/u_ctrl_trx/arb_q_reg*]
  if {[llength $arb]} {
    set_false_path -rise_from [get_clocks $scl_clk] -to $arb
  }
}

#############################
# Internal paths            #
#############################

# Structural constraints inside one I3C instance. These belong in the synthesis
# SDC; the domain-crossing bounds do not, see i3c_set_cdc_bounds.
proc i3c_set_internal_paths {inst clk_name clk_period} {
  set inbufs ${inst}/u_core/u_targ_inbufs

  foreach buf {u_scl_buf u_scl_inv u_sda0_clk u_sda0_clk_n} {
    # Never take the scan branch of the clock mux in functional analysis, so
    # the scan clock does not appear on the bus clock trees.
    #
    # Optional, because the mux does not always present this pin: On the FPGA,
    # prim_clock_mux2 is a BUFGMUX, whose select is a primitive pin rather
    # than `sel_i`, and the lookup finds nothing. This is not an issue since
    # synthesis ties the scan input of the mux to ground and its select to a
    # constant that picks the functional input.
    i3c_case_if_present 0 ${inbufs}/${buf}/u_mux/sel_i 1
  }

  # Keep the quasi-static buffer enable out of timing. The Target input buffers
  # gate the bus clocks with it through a plain AND/OR (i3c_clock_buf_en.sv)
  # rather than an integrated clock gate, which ends up as a tool-named cell
  # next to u_buf and u_mux. The enable only changes while the bus is idle
  # (i3c_target_rst.sv), so the clock gating checks inferred there are not
  # meaningful either; they start at this flop, so the false path removes them
  # too. The same flop also enables the reset detector's buffers (via
  # rstdet_enable_o in i3c_core.sv).
  i3c_try "target buffer enable" {
    set en_q [i3c_get_cells "${inst} buffer enable" \
        ${inst}/u_core/u_targ_rst/buf_en_q_reg*]
    if {[llength $en_q]} {
      set_false_path -from $en_q
    }
  }
}

#############################
# Domain crossings          #
#############################

# Bounds for the crossings between the bus clocks and clk_i. Call this from the
# check-only flow, which times the routed design with the groups removed. The
# set_clock_groups -async on SCL_EXT and SDA would otherwise take precedence and
# make the set_max_delay below useless. The loopback cut in i3c_create_clocks
# stays in place, but it only names SCL_INT, so it leaves these crossings timed.
#
#   inst       path to the i3c primary partition instance
#   prefix     clock name prefix, e.g. I3C0
#   clk_name   name of the clock the IP runs on (`clk_i`)
#   clk_period period of clk_i
proc i3c_set_cdc_bounds {inst prefix clk_name clk_period} {
  set cdc_max [expr {$clk_period * $::i3c_cfg(cdc_fraction)}]

  # Bus clocks to and from clk_i. Every crossing uses either prim_flop_2sync or
  # the toggle handshake in i3c_sync_data, so bounding the data path is enough.
  # Each entry is the prim_flop_2sync instance itself: i3c_sync_data has one
  # per direction, and prim_edge_detector wraps its own in a generate block.
  set syncs {
    u_core/u_sync_ctrl
    u_core/u_sync_targ
    u_core/u_reg_sync
    u_core/u_target/u_in_sync
    u_core/u_target/u_edge_det/g_sync.u_sync
    u_core/u_target/u_trx_rxd_sync/u_sync_tgl_req
  }
  foreach sync_data {
    u_core/u_target/u_targ_txc_sync
    u_core/u_target/u_arb_sync
    u_core/u_target/gen_targ_txd_sync[*].u_targ_txd_sync
  } {
    lappend syncs ${sync_data}/u_sync_tgl_req \
        ${sync_data}/gen_src_toggle.u_sync_tgl_ack
  }
  foreach sync $syncs {
    i3c_try "CDC bound on ${sync}" {
      set endpoints [i3c_get_cells "${inst}/${sync} synchronizer" \
          ${inst}/${sync}/$::i3c_cfg(sync_flop)]
      if {[llength $endpoints]} {
        set_max_delay $cdc_max -to $endpoints
      }
    }
  }

  # i3c_sync_data carries its payload combinationally alongside the toggle, so
  # the data has to be bounded too (i3c_sync_data.sv).
  #
  # The launching clock has to be named. Without it, the bound also lands on the
  # capture enable, which the transceiver derives from the SDA pad, and that
  # path carries the Target's full input delay: a bound of a clk_i period
  # against an input delay of most of an SCL period can never be met. Each
  # instance is therefore bounded from its own source domain.
  foreach {src_clk instances} [list \
      $clk_name {u_targ_txc_sync u_arb_sync gen_targ_txd_sync[*].u_targ_txd_sync} \
      ${prefix}_SCL_EXT {u_trx_rxd_sync}] {
    foreach sync $instances {
      i3c_try "CDC bound on ${sync} payload" {
        set sync_data [i3c_get_cells "${inst}/${sync} payload" \
            ${inst}/u_core/u_target/${sync}/dst_data_q_reg*]
        if {[llength $sync_data]} {
          set_max_delay $cdc_max -from [get_clocks $src_clk] -to $sync_data
        }
      }
    }
  }

  # The Target transceiver's reset is released by a clk_i flop into the
  # SCL/SDA domains (i3c_core.sv).
  i3c_try "transceiver reset bound" {
    set rst_src [i3c_get_cells "${inst} transceiver reset source" \
        ${inst}/u_core/u_targ_rst_src/*reg*]
    if {[llength $rst_src]} {
      set_max_delay $cdc_max -from $rst_src
    }
  }

  # Quasi-static device address and group address configuration, written while
  # the Target is disabled (i3c_target_trx.sv, TODO #31065). These are
  # hierarchical pins on the transceiver boundary, which are not valid
  # endpoints, so bound whatever passes through them instead. Where the
  # hierarchy has been flattened the pins are gone but the nets that feed them
  # survive one level up, under the name they carry in i3c_core.sv.
  foreach {cfg_pin cfg_net} {targ_dev_i targ_dev grp_addr_i grp_addr} {
    i3c_try "quasi-static ${cfg_pin}" {
      set objs [i3c_get_through "${inst} quasi-static ${cfg_pin}" \
          [list pins ${inst}/u_core/u_targ_trx/${cfg_pin}* \
                nets ${inst}/u_core/${cfg_net}*]]
      if {[llength $objs]} {
        set_max_delay $cdc_max -through $objs
      }
    }
  }

  # The START/STOP detectors are clocked by SDA and take SCL as their data
  # (i3c_target_trx.sv). SDA and SCL are separate asynchronous clocks, so this
  # clock-as-data path has to be bounded explicitly. The specification allows
  # tCAS after a START before the first SCL edge, and tCBP before a STOP, which
  # is the window the detectors have to resolve in.
  foreach det {stop_det start_det rep_start_det rep_start_pre} {
    i3c_try "START/STOP detector ${det}" {
      set det_d [i3c_get_cells "${inst} ${det}" \
          ${inst}/u_core/u_targ_trx/${det}_reg*]
      if {[llength $det_d]} {
        set_max_delay $::i3c_cfg(start_stop_max) -to $det_d
      }
    }
  }

  # The detections are consumed by the SCL-clocked Target logic (`started` and
  # the FSM), which is the same crossing the other way: the first SCL edge
  # comes tCAS after a START and tCASr after a repeated START. Only the paths
  # into SCL are bounded here; stop_det also reaches clk_i through u_edge_det,
  # which is bounded above.
  i3c_try "${prefix} START/STOP detections" {
    set det_q [i3c_get_cells "${inst} START/STOP detections" [list \
        ${inst}/u_core/u_targ_trx/stop_det_reg* \
        ${inst}/u_core/u_targ_trx/start_det_reg* \
        ${inst}/u_core/u_targ_trx/rep_start_det_reg*]]
    if {[llength $det_q]} {
      set_max_delay $::i3c_cfg(start_stop_max) -from $det_q \
          -to [get_clocks ${prefix}_SCL_EXT]
    }
  }

  # The HDR Exit and Restart detector (i3c_patt_detector.sv) counts SDA edges
  # while SCL holds it out of reset, and SCL confirms a Restart. Its results go
  # back to the SCL-clocked transceiver (bus_mode_pq and the FSM). These are
  # the same clock-as-data crossings as above, with tDIG_H between the edges of
  # the pattern. The bound into the detector also covers its quasi-static
  # enables.
  i3c_try "${prefix} HDR pattern detector" {
    set patt [i3c_get_cells "${inst} HDR pattern detector" \
        ${inst}/u_core/u_patt_det/*_reg*]
    if {[llength $patt]} {
      set_max_delay $::i3c_cfg(hdr_patt_max) -to $patt
      set_max_delay $::i3c_cfg(hdr_patt_max) -from $patt \
          -to [get_clocks ${prefix}_SCL_EXT]
    }
  }
}

#############################
# Entry point               #
#############################

# Remembers the SCL port per instance, so that the internal constraints can
# reference the chip port rather than a hierarchical pin, which is not a valid
# timing endpoint.
array set ::i3c_scl_port {}

# Constrain one I3C primary partition end to end.
proc i3c_constrain {inst scl_port sda_port prefix clk_pin clk_name clk_period} {
  set ::i3c_scl_port($inst) $scl_port
  i3c_create_clocks $inst $scl_port $sda_port $prefix $clk_pin $clk_name
  i3c_set_io_delays $inst $scl_port $sda_port $prefix $clk_name
  i3c_set_internal_paths $inst $clk_name $clk_period
}
