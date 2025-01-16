// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
import topgen.lib as lib

top_name = top["name"]
modules = []
for addr_space in top["addr_spaces"]:
    addr_space_suffix = lib.get_addr_space_suffix(addr_space)
    modules.append(f"top_{top_name}{addr_space_suffix}")
modules.sort()
%>\
% for module in modules:
pub mod ${module};
% endfor
