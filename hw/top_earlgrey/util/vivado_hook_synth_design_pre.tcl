# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Change the severity of some messages.

# Abort if the boot ROM init file cannot be found. This is normally just a critical warning
# which is easily overlooked. The bitstream can still be generated but is not functional.
set_msg_config -id {[Synth 8-4445]} -new_severity ERROR

# Abort upon inferring latches. This is normally just a warning. We want to avoid that
# code inferring latches ends up in the repo in the first place.
set_msg_config -id {[Synth 8-327]} -new_severity ERROR

# Abort if a create_clock command fails. This typically happens if anchor points for clock
# constraints inside the design change. The failure is normally just reported as a critical
# warning in batch mode which is easily overlooked. The design might still work but some clocks
# will be unconstrained which can lead to other problems later on.
set_msg_config -id {[Vivado 12-4739]} -new_severity ERROR

# Abort if pblock constraints lose their target cells. This can happen if hierarchies change and
# the constraint doesn't get updated.
set_msg_config -id {[Vivado 12-1433]} -new_severity ERROR
