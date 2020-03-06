# TCL file invoked from VCS's simv at run-time using this: -ucli -do <this file>

if { [info exists ::env(VERDI_HOME)] } {
	# Use FSDB for dumping data, but only if we have Verdi set up.

	# Syntax: fsdbDumpfile FSDB_Name [Limit_Size]
	fsdbDumpfile "waves.fsdb"

	# Syntax: fsdbDumpvars [depth] [instance] [option]*
	##############################################################################
	# Option                     Description
	##############################################################################
	# +mda                       Dumps memory and MDA signals in all scopes.
	# +packedmda                 Dumps packed signals
	# +struct                    Dumps structs
	# +skip_cell_instance=mode  Enables or disables cell dumping
	# +strength                  Enables strength dumping
	# +parameter                 Dumps parameters
	# +power                     Dumps power-related signals
	# +trace_process             Dumps VHDL processes
	# +no_functions              Disables dumping of functions
	# +sva                       Dumps assertions
	# +Reg_Only                  Dumps only reg type signals
	# +IO_Only                   Dumps only IO port signals
	# +by_file=<filename>        File to specify objects to add
	# +all                       Dumps memories, MDA signals, structs, unions,power, and packed structs
	fsdbDumpvars 0 core_ibex_tb_top +all
	fsdbDumpSVA 0 core_ibex_tb_top.dut
} else {
	# We don't have VERDI set up, so use VCS's standard dumping format.
	dump -file "waves.vpd"
	dump -add { core_ibex_tb_top } -depth 0 -aggregates -scope "."
}

run
quit
