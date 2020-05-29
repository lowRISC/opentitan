# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Do not print "KERNEL: " in front of messages to ensure user-printed messages
# match the filter expected by the DV environment.
unset  messageprefix
pref.setvalue application/console/general/show-identifier-in-messages false
run -all
endsim
pref.setvalue application/console/general/show-identifier-in-messages true
