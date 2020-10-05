# Copyright lowRISC contributors
# Copyright edalize contributors
# Licensed under the 2-Clause BSD License, see LICENSE.edalize for details.
# SPDX-License-Identifier: BSD-2-Clause
#
# This file was produced by edalize from a template at
# https://github.com/olofk/edalize/blob/592154c50ac40ec86e3d954dd2d300b0573b2c37/edalize/templates/vivado/vivado-program.tcl.j2

set part [lindex $argv 0]
set bitstream [lindex $argv 1]


if {[info exists env(HW_TARGET)]} {
   set explicit_hw_target $env(HW_TARGET)
} else {
   set explicit_hw_target ""
}
if {[info exists env(JTAG_FREQ)]} {
   set jtag_freq $env(JTAG_FREQ)
} else {
   set jtag_freq ""
}

puts "OpenTitan Xilinx FPGA Programming Tool"
puts "======================================"
puts ""
puts "INFO: Programming part $part with bitstream $bitstream"
if { $explicit_hw_target != "" } {
  puts "INFO: Programming target $explicit_hw_target"
}

# Connect to Xilinx Hardware Server. A new instance of the hardware server is
# started on localhost if HW_SERVER_URL is not given, and if no hardware server
# is already running on localhost.
if { [ catch { open_hw_manager } ] } { open_hw }

if {[info exists env(HW_SERVER_URL)]} {
  set hw_server_url $env(HW_SERVER_URL)
  puts "INFO: Connecting to hardware server at $hw_server_url"
  connect_hw_server -url $hw_server_url
} else {
  connect_hw_server
}

if { $explicit_hw_target == "" } {
  set hw_targets [get_hw_targets]
} else {
  set hw_targets [get_hw_targets $explicit_hw_target]
}

if { [llength $hw_targets] == 0 } {
  if { $explicit_hw_target == "" } {
    puts "ERROR: Failed to find any targets"
  } else {
    puts "ERROR: Failed to find target: $target"
  }
}

# Find the first target and device that contains a FPGA $part.
set hw_device_found 0
foreach hw_target $hw_targets {
    puts "INFO: Trying to use hardware target $hw_target"
    current_hw_target $hw_target

    # Open hardware target
    # The Vivado hardware server isn't always able to reliably open a target.
    # Try three times before giving up.
    set hw_target_opened 0
    for {set open_hw_target_try 1} {$open_hw_target_try <= 3} {incr open_hw_target_try} {
        if {[catch {open_hw_target} res_open_hw_target] == 0} {
            set hw_target_opened 1
            break
        }
    }
    if { $hw_target_opened == 0 } {
        puts "WARNING: Unable to open hardware target $hw_target after " \
            "$open_hw_target_try tries. Skipping."
        continue
    }
    puts "INFO: Opened hardware target $hw_target on try $open_hw_target_try."

    # Iterate through all devices and find one which contains $part
    foreach { hw_device } [get_hw_devices] {
        if { [string first [get_property PART $hw_device] $part] == 0 } {
            puts "INFO: Found $part as part of $hw_device."
            current_hw_device $hw_device
            set hw_device_found 1
            break
        }
    }

    if { $hw_device_found == 1 } {
        break
    } else {
        # Close currently tried device, and try with next one.
        puts "INFO: Part not found as part of $hw_target. Trying next device."
        close_hw_target
    }
}
if { $hw_device_found == 0 } {
    puts "ERROR: None of the hardware targets included a $part FPGA part. \
        Check cables and ensure that jumpers are correct for JTAG programming."
    exit 1
}
puts "INFO: Programming bitstream to device $hw_device on target $hw_target."

# Do the programming
current_hw_device $hw_device
set_property PROGRAM.FILE $bitstream [current_hw_device]
if {$jtag_freq != ""} {
  set_property PARAM.FREQUENCY $jtag_freq [get_hw_targets $hw_target]
}
program_hw_devices [current_hw_device]

# Disconnect from Xilinx Hardware Server
close_hw_target
disconnect_hw_server

puts ""
puts "INFO: SUCCESS! FPGA $part successfully programmed with bitstream $bitstream."
