// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
top_name = top["name"]
modules = []
for addr_space in top["addr_spaces"]:
    if addr_space.get('default', False):
        modules.append(f"top_{top_name}")
    else:
        modules.append(f"top_{top_name}_{addr_space['name']}")
modules.sort()
%>\
% for module in modules:
pub mod ${module};
% endfor
