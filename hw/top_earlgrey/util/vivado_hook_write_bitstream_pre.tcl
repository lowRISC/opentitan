# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

send_msg "Designcheck 1-1" INFO "Checking design"

# Ensure the design meets timing
set slack_ns [get_property SLACK [get_timing_paths -delay_type min_max]]
send_msg "Designcheck 1-2" INFO "Slack is ${slack_ns} ns."

if [expr {$slack_ns < 0}] {
  send_msg "Designcheck 1-3" ERROR "Timing failed. Slack is ${slack_ns} ns."
}

# Enable bitstream identification via USR_ACCESS register.
set_property BITSTREAM.CONFIG.USR_ACCESS TIMESTAMP [current_design]

# Dump MMI for Boot ROM.

proc generate_mmi {filename brams designtask_count} {
    send_msg "${designtask_count}-1" INFO "Dumping MMI to ${filename}"

    set workroot [file dirname [info script]]
    set filepath "${workroot}/${filename}"
    set fileout [open $filepath "w"]

    # Calculate the overall address space.
    set space 0
    foreach inst [lsort -dictionary $brams] {
        set slice_begin [get_property ram_slice_begin [get_cells $inst]]
        set slice_end [get_property ram_slice_end [get_cells $inst]]
        if {$slice_begin eq {} || $slice_end eq {}} {
            send_msg "${designtask_count}-2" ERROR "Extraction of ${filename} information failed."
        }
        # The scrambled Boot ROM is actually 39 bits wide but the updatemem tool segfaults
        # for slice sizes not divisible by 8.
        if {[expr {($slice_end - $slice_begin + 1) < 8}]} {
            set slice_end [expr {$slice_begin + 7}]
        }
        set addr_begin [get_property ram_addr_begin [get_cells $inst]]
        set addr_end [get_property ram_addr_end [get_cells $inst]]
        if {$addr_begin eq {} || $addr_end eq {}} {
            send_msg "${designtask_count}-3" ERROR "Extraction of ${filename} MMI information failed."
        }
        # Calculate total number of bits.
        set space [expr {$space + ($addr_end - $addr_begin + 1) * ($slice_end - $slice_begin + 1)}]
    }

    # Generate the MMI.
    set space [expr {($space / 8) - 1}]
    puts $fileout "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    puts $fileout "<MemInfo Version=\"1\" Minor=\"0\">"
    puts $fileout "  <Processor Endianness=\"Little\" InstPath=\"dummy\">"
    puts $fileout "  <AddressSpace Name=\"rom\" Begin=\"0\" End=\"$space\">"
    puts $fileout "      <BusBlock>"

    set part [get_property PART [current_design]]
    foreach inst [lsort -dictionary $brams] {
        set loc [get_property LOC [get_cells $inst]]
        set loc [string trimleft $loc RAMB36_]
        set slice_begin [get_property ram_slice_begin [get_cells $inst]]
        set slice_end [get_property ram_slice_end [get_cells $inst]]
        # The scrambled Boot ROM is actually 39 bits wide but the updatemem tool segfaults
        # for slice sizes not divisible by 4.
        if {[expr {($slice_end - $slice_begin + 1) < 4}]} {
            set slice_end [expr {$slice_begin + 3}]
        }
        set addr_begin [get_property ram_addr_begin [get_cells $inst]]
        set addr_end [get_property ram_addr_end [get_cells $inst]]
        puts $fileout "        <BitLane MemType=\"RAMB32\" Placement=\"$loc\">"
        puts $fileout "          <DataWidth MSB=\"$slice_end\" LSB=\"$slice_begin\"/>"
        puts $fileout "          <AddressRange Begin=\"$addr_begin\" End=\"$addr_end\"/>"
        puts $fileout "          <Parity ON=\"false\" NumBits=\"0\"/>"
        puts $fileout "        </BitLane>"
    }
    puts $fileout "      </BusBlock>"
    puts $fileout "    </AddressSpace>"
    puts $fileout "  </Processor>"
    puts $fileout "<Config>"
    puts $fileout "  <Option Name=\"Part\" Val=\"$part\"/>"
    puts $fileout "</Config>"
    puts $fileout "</MemInfo>"
    close $fileout
    send_msg "${designtask_count}-4" INFO "MMI dumped to ${filepath}"
}

set brams [split [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ BMEM.bram.* && NAME =~ *u_rom_ctrl*}] " "]
generate_mmi "rom.mmi" $brams 1

set brams [split [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ BMEM.bram.* && NAME =~ *u_otp_ctrl*}] " "]
generate_mmi "otp.mmi" $brams 2
