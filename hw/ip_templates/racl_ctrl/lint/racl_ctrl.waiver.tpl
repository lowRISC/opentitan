# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# waiver file for ${module_instance_name}

waive -rules {HIER_NET_NOT_READ} -location {${module_instance_name}_reg_top.sv} -regexp {error_log_flds_we\[4:1\]' is not read from in module} ${"\\"}
      -comment "Internal register is accepted to not be read. Tracked in #25663."
