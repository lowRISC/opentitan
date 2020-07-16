# Copyright 2020 ETH Zurich and University of Bologna.
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.

# Author: Robert Balas (balasr@iis.ee.ethz.ch)
# Description: TCL scripts to facilitate simulations
# catch {
#     if {$trdb_all ne ""} {
#	foreach inst $trdb_all {
#	    add wave -group [file tail $inst] $inst/*
#	}
#     }
# } err

# if {$err ne ""} {
#     puts "\[TCL\]: Suppressed error: $err"
# }

# add fc
set rvcores [find instances -recursive -bydu riscv_core -nodu]
set fpuprivate [find instances -recursive -bydu fpu_private]
set tb_top [find instances -recursive -bydu tb_top -nod]
set mm_ram [find instances -recursive -bydu mm_ram -nod]
set dp_ram [find instances -recursive -bydu dp_ram -nod]

if {$tb_top ne ""} {
    foreach inst $tb_top {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$mm_ram ne ""} {
    foreach inst $mm_ram {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$dp_ram ne ""} {
    foreach inst $dp_ram {
	add wave -group [file tail $inst] $inst/*
    }
}

if {$rvcores ne ""} {
  set rvprefetch [find instances -recursive -bydu riscv_prefetch_L0_buffer -nodu]

  add wave -group "Core"                                     $rvcores/*
  add wave -group "IF Stage" -group "Hwlp Ctrl"              $rvcores/if_stage_i/hwloop_controller_i/*
  if {$rvprefetch ne ""} {
    add wave -group "IF Stage" -group "Prefetch" -group "L0"   $rvcores/if_stage_i/prefetch_128/prefetch_buffer_i/L0_buffer_i/*
    add wave -group "IF Stage" -group "Prefetch"               $rvcores/if_stage_i/prefetch_128/prefetch_buffer_i/*
  } {
    add wave -group "IF Stage" -group "Prefetch" -group "FIFO" $rvcores/if_stage_i/prefetch_32/prefetch_buffer_i/fifo_i/*
    add wave -group "IF Stage" -group "Prefetch"               $rvcores/if_stage_i/prefetch_32/prefetch_buffer_i/*
  }
  add wave -group "IF Stage"                                 $rvcores/if_stage_i/*
  add wave -group "ID Stage"                                 $rvcores/id_stage_i/*
  add wave -group "RF"                                       $rvcores/id_stage_i/registers_i/riscv_register_file_i/mem
  add wave -group "RF_FP"                                    $rvcores/id_stage_i/registers_i/riscv_register_file_i/mem_fp
  add wave -group "Decoder"                                  $rvcores/id_stage_i/decoder_i/*
  add wave -group "Controller"                               $rvcores/id_stage_i/controller_i/*
  add wave -group "Int Ctrl"                                 $rvcores/id_stage_i/int_controller_i/*
  add wave -group "Hwloop Regs"                              $rvcores/id_stage_i/hwloop_regs_i/*
  add wave -group "EX Stage" -group "ALU"                    $rvcores/ex_stage_i/alu_i/*
  add wave -group "EX Stage" -group "ALU_DIV"                $rvcores/ex_stage_i/alu_i/int_div/div_i/*
  add wave -group "EX Stage" -group "MUL"                    $rvcores/ex_stage_i/mult_i/*
  if {$fpuprivate ne ""} {
    add wave -group "EX Stage" -group "APU_DISP"             $rvcores/ex_stage_i/genblk1/apu_disp_i/*
    add wave -group "EX Stage" -group "FPU"                  $rvcores/ex_stage_i/genblk1/genblk1/fpu_i/*
  }
  add wave -group "EX Stage"                                 $rvcores/ex_stage_i/*
  add wave -group "LSU"                                      $rvcores/load_store_unit_i/*
  add wave -group "CSR"                                      $rvcores/cs_registers_i/*
}

# add dm
set dm [find instances -recursive -bydu dm_top -nodu]
set dm_mem  [find instances -recursive -bydu dm_mem -nodu]
set dm_csrs [find instances -recursive -bydu dm_csrs -nodu]
set dm_sba  [find instances -recursive -bydu dm_sba -nodu]

if {$dm ne ""} {
  add wave -group "DM"                                     $dm/*
}
if {$dm_mem ne ""} {
  add wave -group "DM" -group "dm_mem"                     $dm_mem/*
}
if {$dm_csrs ne ""} {
  add wave -group "DM" -group "dm_csrs"                    $dm_csrs/*
}
if {$dm_sba ne ""} {
  add wave -group "DM" -group "dm_sba"                     $dm_sba/*
}

# add dmi_jtag
set dmi [find instances -recursive -bydu dmi_jtag -nodu]
set dmi_tap  [find instances -recursive -bydu dmi_jtag_tap -nodu]

if {$dmi ne ""} {
  add wave -group "DMI"                                     $dmi/*
}
if {$dmi_tap ne ""} {
  add wave -group "DMI" -group "dmi_tap"                    $dmi_tap/*
}


configure wave -namecolwidth  250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -timelineunits ns
