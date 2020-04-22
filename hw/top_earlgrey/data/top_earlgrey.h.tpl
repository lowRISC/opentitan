// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _TOP_EARLGREY_H_
#define _TOP_EARLGREY_H_

#define PINMUX_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO ${top["pinmux"]["num_mio"]}
#define NUM_DIO ${sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["dio"]])}

<% offset = 0 %>\
% for i, sig in enumerate(top["pinmux"]["inouts"] + top["pinmux"]["inputs"]):
  % if sig["width"] == 1:
#define PINMUX_${sig["name"].upper()}_IN ${offset + i}
  % else:
    % for j in range(sig["width"]):
#define PINMUX_${sig["name"].upper()}_${j}_IN ${offset + i + j}
    % endfor
<% offset += sig["width"] %>\
  % endif
% endfor

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

// PERIPH_OUTSEL ranges from 0 to NUM_MIO + 3 -1}
// 0, 1 and 2 are tied to value 0, 1 and high-impedance

## offset starts from 3 as 0, 1, 2 are prefixed value
<% offset = 3 %>\
#define PINMUX_VALUE_0_OUT 0
#define PINMUX_VALUE_1_OUT 1
#define PINMUX_VALUE_Z_OUT 2
% for i, sig in enumerate(top["pinmux"]["inouts"] + top["pinmux"]["outputs"]):
  % if sig["width"] == 1:
#define PINMUX_${sig["width"].upper()}_OUT ${offset + i}
  % else:
    % for j in range(sig["width"]):
#define PINMUX_${sig["name"].upper()}_${j}_OUT ${offset + i + j}
    % endfor
<% offset += sig["width"] %>\
  % endif
% endfor

<%!

def camelcase(str):
    """Turns a string from 'snake_case' to 'CamelCase'."""
    return "".join([part.capitalize() for part in str.split("_")])

periperhal_enum_prefix = "kTopEarlgreyPlicPeripheral"
def peripheral_enum_name(module_name):
    """Generate name for a peripheral"""
    return periperhal_enum_prefix + camelcase(module_name)

interrupt_id_enum_prefix = "kTopEarlgreyPlicIrqId"
def interrupt_id_enum_name(intr_name, intr_num=None):
    """Generate name for an interrupt id (intr_name is prefixed with the module
    name)"""
    if intr_num is not None:
        return interrupt_id_enum_prefix + camelcase(intr_name) + str(intr_num)
    else:
        return interrupt_id_enum_prefix + camelcase(intr_name)

%>\
## This dictionary will be used in the C implementation to generate
## `top_earlgrey_plic_interrupt_for_peripheral`.
<% c_gen_info["interrupt_id_map"] = {} %>\
/**
 * PLIC Interrupt source peripheral enumeration.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_earlgrey_plic_peripheral {
  ${peripheral_enum_name("unknown")} = 0, /**< Unknown Peripheral */
<% enum_id = 1 %>\
% for mod_name in top["interrupt_module"]:
  ${peripheral_enum_name(mod_name)} = ${enum_id}, /**< ${mod_name} */
<% enum_id += 1 %>\
% endfor
  ${peripheral_enum_name("last")} = ${enum_id - 1}, /**< \internal Final PLIC peripheral */
} top_earlgrey_plic_peripheral_t;

/**
 * PLIC Interrupt Ids Enumeration
 *
 * Enumeration of all PLIC interrupt source IDs. The IRQ IDs belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_plic_irq_id {
  ${interrupt_id_enum_name("none")} = 0, /**< No Interrupt */
<% c_gen_info["interrupt_id_map"][interrupt_id_enum_name("none")] = peripheral_enum_name("unknown") %>\
<% enum_id = 1 %>\
% for intr in top["interrupt"]:
    % if "width" in intr and int(intr["width"]) != 1:
        % for i in range(int(intr["width"])):
  ${interrupt_id_enum_name(intr["name"], i)} = ${enum_id}, /**< ${intr["name"]} ${i} */
<% c_gen_info["interrupt_id_map"][interrupt_id_enum_name(intr["name"], i)] = peripheral_enum_name(intr["module_name"]) %>\
<% enum_id += 1 %>\
        % endfor
    % else:
  ${interrupt_id_enum_name(intr["name"])} = ${enum_id}, /**< ${intr["name"]} */
<% c_gen_info["interrupt_id_map"][interrupt_id_enum_name(intr["name"])] = peripheral_enum_name(intr["module_name"]) %>\
<% enum_id += 1 %>\
    % endif
% endfor
  ${interrupt_id_enum_name("last")} = ${enum_id - 1}, /**< \internal The Last Valid Interrupt ID. */
} top_earlgrey_plic_irq_id_t;

/**
 * PLIC Interrupt Id to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
extern const top_earlgrey_plic_peripheral_t
  top_earlgrey_plic_interrupt_for_peripheral[${len(c_gen_info["interrupt_id_map"])}];

/**
 * PLIC external interrupt target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access dependent on the target.
 */
typedef enum top_earlgrey_plic_target {
<% enum_id = 0 %>\
% for core_id in range(int(top["num_cores"])):
  kTopEarlgreyPlicTargetIbex${core_id} = ${enum_id}, /**< Ibex Core ${core_id} */
<% enum_id += 1 %>\
% endfor
  kTopEarlgreyPlicTargetLast = ${enum_id - 1}, /**< \internal Final PLIC target */
} top_earlgrey_plic_target_t;

#endif  // _TOP_EARLGREY_H_
