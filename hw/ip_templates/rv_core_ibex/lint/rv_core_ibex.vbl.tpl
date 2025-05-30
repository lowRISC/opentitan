# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# waiver file for ${module_instance_name}

# Waive Ibex formal DV environment
waive --rule=interface-name-style --location="mem.sv"
waive --rule=module-port --location="spec_instance.sv"
