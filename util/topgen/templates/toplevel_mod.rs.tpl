// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
    top_name = top["name"]
    modules = []
    for addr_space in top["addr_spaces"]:
        if addr_space.get('default', False):
            modules.append(f"top_{top_name}")
            modules.append(f"top_{top_name}_memory")
        else:
            addr_space_name = addr_space["name"]
            modules.append(f"top_{top_name}_{addr_space['name']}")
            modules.append(f"top_{top_name}_{addr_space['name']}_memory")
    modules.sort()
%>\
% for module in modules:
pub mod ${module};
% endfor
