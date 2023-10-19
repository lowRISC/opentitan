// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
<%
from topgen.lib import Name, is_top_reggen, is_ipgen

module_types = {m["type"] for m in top["module"]}
module_types = sorted(module_types)
top_reggen_module_types = {m["type"] for m in top["module"] if is_top_reggen(m)}
ipgen_module_types = {m["type"] for m in top["module"] if is_ipgen(m)}
top_name = Name(["top", top["name"]])
irq_base_name = top_name + Name(["plic", "irq", "id"])
top_clock_prefix = top_name + Name(["clock", "src"])
module_data = {}
%>\

#include "sw/device/lib/devicetables/dt.h"

#include "hw/top_${top["name"]}/sw/autogen/top_${top["name"]}.h"
% for header_path in sorted(dt_headers):
#include "${header_path}"
% endfor

//#include <assert.h>
#include <stdint.h>

% for module_name in module_types:
// Device tables for ${module_name}
%   if module_name in top_reggen_module_types:
// TODO: Handle tables for top_reggen types
<%    continue %>\
%   endif
<%
    modules = [m for m in top["module"] if m["type"] == module_name]
    block = name_to_block[module_name]
    dev_type_enum = Name.from_snake_case(
        "dt_device_type_{}".format(module_name)
    ).as_c_enum()
    dev_base_enum = Name.from_snake_case(
        "dt_device_id_base_{}".format(module_name)
    ).as_c_enum()
    dev_count_enum = Name.from_snake_case(
        "dt_device_count_{}".format(module_name)
    ).as_c_enum()
    reg_count_enum = Name.from_snake_case(
        "dt_{}_reg_block_count".format(module_name)
    ).as_c_enum()
    clk_count_enum = Name.from_snake_case(
        "dt_{}_clock_count".format(module_name)
    ).as_c_enum()
    irq_count_enum = Name.from_snake_case(
        "dt_{}_irq_type_count".format(module_name)
    ).as_c_enum()
    reg_count = len(block.reg_blocks)
    irq_count = 0
    for irq in block.interrupts:
      irq_count += irq.bits.width()
    irqs = {}
    for m in modules:
      irqs_packed = [irq
        for irq in top["interrupt"] if irq["module_name"] == m["name"]]
      irqs[m["name"]] = []
      for irq in irqs_packed:
        irq_name = irq_base_name + Name.from_snake_case(irq["name"])
        irq_width = int(irq["width"])
        if irq_width > 1:
          for i in range(irq_width):
            irqs[m["name"]].append(irq_name + Name([str(i)]))
        else:
          irqs[m["name"]].append(irq_name)
    block_clock_prefix = Name.from_snake_case(f"dt_{module_name}_clock")
    block_clocks = {}
    for clock in block.clocking.items:
        if clock.internal or clock.clock == None or clock.clock == "scan_clk_i":
            continue
        if clock.clock_base_name == "":
            block_clock = block_clock_prefix + Name(["clk"])
        else:
            block_clock = (block_clock_prefix +
                           Name.from_snake_case(clock.clock_base_name))
        block_clocks[clock.clock] = block_clock
    clk_count = len(block_clocks.keys())
    module_data[module_name] = {
        "dev_type": dev_type_enum,
        "dev_count": dev_count_enum,
        "reg_count": reg_count_enum,
        "clk_count": clk_count_enum,
        "irq_count": irq_count_enum,
        "num_irq": irq_count,
    }
%>\
%   if reg_count > 0:
_Static_assert(${reg_count_enum} == ${str(reg_count)}, "Reg block count mismatch");
%   endif
%   if clk_count > 0:
_Static_assert(${clk_count_enum} == ${str(clk_count)}, "Clock count mismatch");
%   endif
%   if irq_count > 0:
_Static_assert(${irq_count_enum} == ${str(irq_count)}, "IRQ count mismatch");
%   endif

typedef struct dt_${module_name}_info {
  uint32_t base_addrs[${reg_count_enum}];
  dt_clock_t clocks[${clk_count_enum}];
% if len(block.interrupts) > 0:
  uint32_t irqs[${irq_count_enum}];
% endif
} dt_${module_name}_info_t;

static const dt_${module_name}_info_t dev_table_${module_name}[${dev_count_enum}] = {
%   for m in modules:
    // Properties for ${m["name"]}
    {
        .base_addrs = {
%     for addr in m["base_addrs"].values():
            ${addr},
%     endfor
        },
        .clocks = {
%     for port, clock in m["clock_srcs"].items():
%       if port in block_clocks:
<%
        if type(clock) is str:
            clock_id = top_clock_prefix + Name.from_snake_case(clock)
        else:
            clock_id = top_clock_prefix + Name.from_snake_case(clock["clock"])
        block_clock_enum = block_clocks[port].as_c_enum()
%>\
            [${block_clock_enum}] = ${clock_id.as_c_enum()},
%       endif
%     endfor
        },
%   if len(block.interrupts) > 0:
        .irqs = {
%     for irq in irqs[m["name"]]:
            ${irq.as_c_enum()},
%     endfor
        },
%   endif
    },
%   endfor
};
% endfor

<%
    dev_prefix = Name(["dt", "device", "id"])
    irq_prefix = Name(["top", top["name"], "plic", "irq", "id"])
    none_irq_name = irq_prefix + Name(["None"])
    unknown_peripheral_name = dev_prefix + Name(["unknown"])
    irq_table = {none_irq_name: unknown_peripheral_name}
    for module_name, irqs in helper.device_irqs.items():
        dev_name = Name.from_snake_case(module_name)
        for irq in irqs:
            irq_name = irq_prefix + Name.from_snake_case(irq)
            irq_table[irq_name] = dev_prefix + dev_name
    id_base_prefix = Name(["dt", "device", "id", "base"])
    dev_type_prefix = Name(["dt", "device", "type"])
    count_prefix = Name(["dt", "device", "count"])
%>\

/**
 * A set of tables containing top-level device info. The tables represent a
 * flattened tree of tables that group info by device type. A given device's
 * associated info is located at the base index for that device type's table,
 * plus the number of such devices that were in the top-level hjson file before
 * the given device.
 */
typedef struct top_device_table {
  uint32_t dev_type_base[kDtDeviceTypeCount];
  uint32_t dev_type_len[kDtDeviceTypeCount];
  dt_device_type_t device_type[kDtDeviceIdCount];
} top_device_table_t;

static const top_device_table_t devices = {
    .dev_type_base = {
% for dev_type in helper.device_id_groups.keys():
        [${(dev_type_prefix + dev_type).as_c_enum()}] = ${(id_base_prefix + dev_type).as_c_enum()},
% endfor
    },
    .dev_type_len = {
% for dev_type in helper.device_id_groups.keys():
        [${(dev_type_prefix + dev_type).as_c_enum()}] = ${(count_prefix + dev_type).as_c_enum()},
% endfor
    },
    .device_type = {
% for dev_type, (_, dev_list) in helper.device_id_groups.items():
%   for dev_name in dev_list:
        [${(dev_prefix + dev_name).as_c_enum()}] = ${(dev_type_prefix + dev_type).as_c_enum()},
%   endfor
% endfor
    },
};

uint32_t dt_num_devices(dt_device_type_t dev_type) {
  if (dev_type < kDtDeviceTypeCount) {
    return devices.dev_type_len[dev_type];
  }
  return 0;
}

dt_device_t dt_get_device(dt_device_type_t dev_type, uint16_t dev_idx) {
  if (dev_type < kDtDeviceTypeCount) {
    if (dev_idx < devices.dev_type_len[dev_type]) {
      return devices.dev_type_base[dev_type] + dev_idx;
    }
  }
  return kDtDeviceUnknown;
}

inline dt_device_type_t __dt_device_get_type(dt_device_t dev) {
  dt_device_type_t dev_type = kDtDeviceTypeUnknown;
  if (dev < kDtDeviceIdCount) {
    switch (dev) {
% for dev_type, (_, dev_list) in helper.device_id_groups.items():
<%  if dev_type.as_snake_case() == "unknown": continue %>\
%   for dev_name in dev_list:
      case ${(dev_prefix + dev_name).as_c_enum()}:
        dev_type = ${(dev_type_prefix + dev_type).as_c_enum()};
        break;
%   endfor
% endfor
      default:
        break;
    }
  }
  return dev_type;
}

inline uint32_t __dt_device_get_index(dt_device_t dev) {
  if (dev < kDtDeviceIdCount) {
    switch (dev) {
% for dev_type, (_, dev_list) in helper.device_id_groups.items():
<%  if dev_type.as_snake_case() == "unknown": continue %>\
%   for dev_idx, dev_name in enumerate(dev_list):
      case ${(dev_prefix + dev_name).as_c_enum()}:
        return ${dev_idx};
%   endfor
% endfor
      default:
        break;
    }
  }
  return 0;
}

dt_device_type_t dt_device_get_type(dt_device_t dev) {
  return __dt_device_get_type(dev);
}

uintptr_t dt_device_reg_addr(dt_device_t dev, uint32_t reg_block_idx) {
  if (dev < kDtDeviceIdCount) {
    uint32_t dev_idx = __dt_device_get_index(dev);
    dt_device_type_t dev_type = __dt_device_get_type(dev);
    if (dev_type < kDtDeviceTypeCount) {
      switch (dev_type) {
% for module_name, data in module_data.items():
        case ${data["dev_type"]}:
          if (reg_block_idx < ${data["reg_count"]}) {
              return dev_table_${module_name}[dev_idx].base_addrs[reg_block_idx];
          }
          break;
% endfor
        default:
          break;
      }
    }
  }
  return 0;
}

uint32_t dt_device_irq_id(dt_device_t dev, uint32_t irq_type) {
  if (dev < kDtDeviceIdCount) {
    uint32_t dev_idx = __dt_device_get_index(dev);
    dt_device_type_t dev_type = __dt_device_get_type(dev);
    if (dev_type < kDtDeviceTypeCount) {
      switch (dev_type) {
% for module_name, data in module_data.items():
%   if len(name_to_block[module_name].interrupts) > 0:
        case ${data["dev_type"]}:
          if (irq_type < ${data["irq_count"]}) {
              return dev_table_${module_name}[dev_idx].irqs[irq_type];
          }
          break;
%   endif
% endfor
        default:
          break;
      }
    }
  }
  return kDtIrqUnknown;
}

dt_clock_t dt_device_clock_id(dt_device_t dev, uint32_t clock_port) {
  if (dev < kDtDeviceIdCount) {
    uint32_t dev_idx = __dt_device_get_index(dev);
    dt_device_type_t dev_type = __dt_device_get_type(dev);
    if (dev_type < kDtDeviceTypeCount) {
      switch (dev_type) {
% for module_name, data in module_data.items():
        case ${data["dev_type"]}:
          if (clock_port < ${data["clk_count"]}) {
              return dev_table_${module_name}[dev_idx].clocks[clock_port];
          }
          break;
% endfor
        default:
          break;
      }
    }
  }
  return kDtClockUnknown;
}

enum {
  kDtIrqIdCount = ${str(len(irq_table.keys()))},
};

static const dt_device_t device_from_irq[kDtIrqIdCount] = {
% for irq, device_id in irq_table.items():
    [${irq.as_c_enum()}] = ${device_id.as_c_enum()},
% endfor
};

/**
 * Return device ID for a given peripheral
 */
dt_device_t dt_irq_to_device(uint32_t irq) {
  if (irq < kDtIrqIdCount) {
    return device_from_irq[irq];
  }
  return kDtDeviceUnknown;
}
