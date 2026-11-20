# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
################################################################################
#
# TCL script to setup a default waves dump of one single scope in simulation
#
################################################################################

# First, check the wave-file format / simulator combination are compatible
checkWaveformFileCompat $simulator $waves

# A global variable representing the file id (fid) of the waves dumped in VPD format.
setDefault vpd_fid 0

# Open a default database to capture the probed waveforms into
set wavedump_db "waves.$waves"
waveOpenDB $wavedump_db $waves $simulator

# Add a waveform probe starting at the scope of $tb_top, with infinite depth
wavedumpScope $waves $simulator $scope 0

puts "INFO: Dumping to $wavedump_db the full-depth scope of $scope"
