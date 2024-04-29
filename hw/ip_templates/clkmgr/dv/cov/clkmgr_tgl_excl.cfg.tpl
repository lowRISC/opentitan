// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//======================================================================
// This file contains outputs of clkmgr tied to constants.
//======================================================================

% for k in typed_clocks['ft_clks']:
-module_node clkmgr cg_en_o.${k.split('clk_')[-1]}
% endfor
