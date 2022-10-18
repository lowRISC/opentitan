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

# Generate an MMI file for the given BRAM cells.
#
# Args:
#   filename:            Path to the output file.
#   brams:               A list of BRAM cells.
#   mem_type:            The BRAM type, e.g. "RAMB36".
#   fake_word_width:     If non-zero, pretend that $brams covers
#                        `fake_word_width` bits. Influences the values of the
#                        MMI's <AddressSpace> and <DataWidth> tags.
#   addr_end_multiplier: A coefficient applied to the address space. Influences
#                        the values of the MMI's <AddressSpace> and
#                        <AddressRange> tags.
#   designtask_count:    A number used for logging with `send_msg`.
proc generate_mmi {filename brams mem_type fake_word_width addr_end_multiplier designtask_count} {
    send_msg "${designtask_count}-1" INFO "Dumping MMI to ${filename}"

    if {[llen $brams] == 0} {
        send_msg "${designtask_count}-1" INFO "Cannot make MMI for zero BRAMs"
        return
    }

    set workroot [file dirname [info script]]
    set filepath "${workroot}/${filename}"
    set fileout [open $filepath "w"]

    set fake_slice_width [expr $fake_word_width / [llen $brams]]

    # Calculate the overall address space.
    set space 0
    foreach inst [lsort -dictionary $brams] {
        set slice_begin [get_property ram_slice_begin [get_cells $inst]]
        set slice_end [get_property ram_slice_end [get_cells $inst]]
        if {$slice_begin eq {} || $slice_end eq {}} {
            send_msg "${designtask_count}-2" ERROR "Extraction of ${filename} information failed."
        }
        set slice_width [expr {$slice_end - $slice_begin + 1}]
        if {$slice_width < $fake_slice_width} {
            set slice_end [expr {$slice_begin + $fake_slice_width - 1}]
            set slice_width $fake_slice_width
        }
        set addr_begin [get_property ram_addr_begin [get_cells $inst]]
        set addr_end [get_property ram_addr_end [get_cells $inst]]
        if {$addr_begin eq {} || $addr_end eq {}} {
            send_msg "${designtask_count}-3" ERROR "Extraction of ${filename} MMI information failed."
        }

        # Calculate total number of bits.
        set space [expr {$space + ($addr_end - $addr_begin + 1) * $slice_width}]
        set last_slice_width $slice_width
    }
    set space [expr {($space * $addr_end_multiplier / 8) - 1}]

    # Generate the MMI.
    puts $fileout "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    puts $fileout "<MemInfo Version=\"1\" Minor=\"1\">"
    puts $fileout "  <Processor Endianness=\"Little\" InstPath=\"dummy\">"
    puts $fileout "  <AddressSpace Name=\"dummy_addrspace\" Begin=\"0\" End=\"$space\">"
    puts $fileout "      <BusBlock>"

    set loc_prefix "${mem_type}_"

    set part [get_property PART [current_design]]
    foreach inst [lsort -dictionary $brams] {
        set loc [get_property LOC [get_cells $inst]]
        set loc [string trimleft $loc $loc_prefix]
        set slice_begin [get_property ram_slice_begin [get_cells $inst]]
        set slice_end [get_property ram_slice_end [get_cells $inst]]
        set slice_width [expr {$slice_end - $slice_begin + 1}]
        if {$slice_width < $fake_slice_width} {
            set slice_end [expr {$slice_begin + $fake_slice_width - 1}]
            set slice_width $fake_slice_width
        }
        set addr_begin [get_property ram_addr_begin [get_cells $inst]]
        set addr_end [get_property ram_addr_end [get_cells $inst]]
        set addr_end [expr {($addr_end + 1) * $addr_end_multiplier - 1}]
        puts $fileout "        <BitLane MemType=\"$mem_type\" Placement=\"$loc\">"
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

# Dump INIT_XX strings for the given BRAMs to an output file.
#
# In the output file, the BRAMs and their INIT_XX strings will be sorted in
# increasing order. This proc is a time-saver because the Vivado GUI's property
# viewer does not sort the INIT_XX strings numerically.
#
# Args:
#   filename:         Where to write
#   brams:            A list of BRAM cells.
#   designtask_count: A number used for logging with `send_msg`.
proc dump_init_strings {filename brams designtask_count} {
    # For each OTP BRAM, dump all the INIT_XX strings.
    send_msg "${designtask_count}-1" INFO "Dumping INIT_XX strings to ${filename}"

    set workroot [file dirname [info script]]
    set filepath "${workroot}/${filename}"
    set fileout [open $filepath "w"]

    foreach inst [lsort -dictionary $brams] {
        set bram [get_cells $inst]

        set loc [get_property LOC $bram]
        puts $fileout "LOC: $loc"

        set init_count 0
        while 1 {
            set key [format "INIT_%.2X" $init_count]
            if { [llength [list_property $bram $key]] eq 0 } {
                break
            }
            set val [get_property $key $bram]
            puts $fileout "$key $val"
            incr init_count
        }

        puts $fileout ""
    }
    close $fileout
    send_msg "${designtask_count}-4" INFO "INIT_XX strings dumped to ${filepath}"
}

# The scrambled Boot ROM is actually 39 bits wide, but we need to pretend that
# it's 40 bits, or else we will be unable to encode our ROM data in a MEM file
# that updatemem will understand.
#
# Suppose we did not pad the width, leaving it at 39 bits. Now, if we encode a
# word as a 10-digit hex string, updatemem would splice an additional zero bit
# into the bitstream because each hex digit is strictly 4 bits. If we wrote four
# words at a time, as a 39-digit hex string (39*4 is nicely divisible by 4),
# updatemem would fail to parse the hex string, saying something like "Data
# segment starting at 0x00000000, has exceeded data limits." The longest hex
# string it will accept is 16 digits, or 64 bits.
#
# A hack that works is to pretend the data width is actually 40 bits. Updatemem
# seems to write that extra zero bit into the ether without complaint.
set rom_brams [split [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ BMEM.bram.* && NAME =~ *u_rom_ctrl*}] " "]
generate_mmi "rom.mmi" $rom_brams "RAMB36" 40 1 1

# OTP does not require faking the word width, but it has its own quirk. It seems
# each 22-bit OTP word is followed by 15 zero words. The MMI's <AddressSpace>
# and <AddressRange> tags need to account for this or else updatemem will think
# that its data input overruns the address space. The workaround is to pretend
# the address space is 16 times larger than we would normally compute.
set otp_brams [split [get_cells -hierarchical -filter { PRIMITIVE_TYPE =~ BMEM.bram.* && NAME =~ *u_otp_ctrl*}] " "]
generate_mmi "otp.mmi" $otp_brams "RAMB18" 0 16 2

# For debugging purposes, dump the INIT_XX strings for ROM and OTP.
dump_init_strings "rom_init_strings.txt" $rom_brams 3
dump_init_strings "otp_init_strings.txt" $otp_brams 4
