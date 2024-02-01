# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This file sets common message configurations for all VC Formal tcl files.

# Change severity level to Error for specific messages:
# Command: set_message_severity -names message_names error


# Disable specific Warning messages:
# Command: suppress_message [MESSAGE NAMES]

#Warning-[SM_UST] Unsupported System Task
suppress_message SM_UST

#Warning-[SVAC-IAAB] Immediate assert action block
suppress_message SVAC-IAAB

#Warning-[SM_IGN_FINAL] Ignoring not supported "final" block
suppress_message SM_IGN_FINAL

#[Warning] PROP_W_ENCODING_NOT_FOUND: Property ... has no encoding for specified usage assert and is ignored.
suppress_message PROP_W_ENCODING_NOT_FOUND
