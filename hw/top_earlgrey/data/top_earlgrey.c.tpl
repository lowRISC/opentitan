// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "${c_gen_info["header_path"]}"

/**
 * PLIC Interrupt Id to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
const top_earlgrey_plic_peripheral_t
    top_earlgrey_plic_interrupt_for_peripheral[${len(c_gen_info["interrupt_id_map"])}] = {
% for (irq_id_name, module_name) in c_gen_info["interrupt_id_map"].items():
  [${irq_id_name}] = ${module_name},
%endfor
};
