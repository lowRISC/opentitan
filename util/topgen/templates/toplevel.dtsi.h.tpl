// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/dts-v1/;

% if helper.pinmux_peripheral_in is not None:
/**
 * Pinmux peripheral input mux IDs.
 */
%   for name, value, docstring in helper.pinmux_peripheral_in.constants[:-1]:
/** ${docstring} */
#define ${name.as_c_define()} ${value}
%   endfor
% endif

% if helper.pinmux_insel is not None:
/**
 * Pinmux input selection IDs for pads or tied values.
 */
%   for name, value, docstring in helper.pinmux_insel.constants[:-1]:
/** ${docstring} */
#define ${name.as_c_define()} ${value}
%   endfor
% endif

% if helper.pinmux_mio_out is not None:
/**
 * Pinmux pad output mux IDs.
 */
%   for name, value, docstring in helper.pinmux_mio_out.constants[:-1]:
/** ${docstring} */
#define ${name.as_c_define()} ${value}
%   endfor
% endif

% if helper.pinmux_outsel is not None:
/**
 * Pinmux output selection IDs for peripherals or tied values.
 */
%   for name, value, docstring in helper.pinmux_outsel.constants[:-1]:
/** ${docstring} */
#define ${name.as_c_define()} ${value}
%   endfor
% endif

#define OPENTITAN_PINMUX(mux_id, select_id) \
    ((mux_id << 16) | (select_id))

/ {
    #address-cells = <1>;
    #size-cells = <1>;
    model = "lowrisc,${top["name"].lower()}";
    compatible = "lowrisc,${top["name"].lower()}";

    cpus {
        #address-cells = <1>;
        #size-cells = <0>;

        hart0: cpu@0 {
            compatible = "riscv";
            device_type = "cpu";
            reg = <0>;
            status = "okay";

            hlic: interrupt-controller {
                compatible = "riscv,cpu-intc";
                #interrupt-cells = <1>;
                interrupt-controller;
            };
        };
    };

% for name, region in helper.memories():
<%
    hex_base_addr = "{:#010x}".format(region.base_addr)
    hex_size_bytes = "{:#010x}".format(region.size_bytes)
%>\
    /**
     * Memory for ${name} in top ${top["name"]}.
     */
    ${name}: memory@${hex_base_addr} {
        device_type = "memory";
        reg = <${hex_base_addr} ${hex_size_bytes}>;
    };

% endfor

    bus {
        compatible = "simple-bus";
        #address-cells = <1>;
        #size-cells = <1>;
        ranges;

<%
  # This will seed the device_regions dictionary.
  devices = helper.devices()
  interrupts = {}
  for m in top["interrupt_module"]:
    interrupts[m] = []
  irq_id = 1
  for irq in top["interrupt"]:
    inst_name = irq["module_name"]
    # Remove "{inst_name}_" prefix
    prefix_len = len(inst_name) + 1
    irq_name = irq["name"][prefix_len:]
    irq_width = int(irq["width"])
    if irq_width > 1:
      for sub_irq in range(irq_width):
        sub_irq_name = "{}{}".format(irq_name, sub_irq)
        interrupts[inst_name].append((sub_irq_name, irq_id))
        irq_id += 1
    else:
      interrupts[inst_name].append((irq_name, irq_id))
      irq_id += 1
  # TODO: Don't hard-code interrupt controller name and max prio.
  plic_name = "rv_plic"
  plic_max_prio = 3
  plic_num_irqs = irq_id
%>\
% for m in top["module"]:
<%
  inst_name = m["name"]
  inst_type = m["type"]
  device_regions = helper.device_regions[inst_name]
  if None in device_regions:
    base_addr = device_regions[None].base_addr
  elif 'core' in device_regions:
    base_addr = device_regions['core'].base_addr
  else:
    base_addr = sorted([x.base_addr for x in device_regions.values()])[0]
  regs = []
  reg_names = []
  for reg_name, reg in device_regions.items():
    regs.append(reg)
    reg_names.append(reg_name)
  base_addr = "{:#010x}".format(base_addr)
%>\
        ${inst_name}: ${inst_type}@${base_addr} {
%   if inst_name == plic_name:
            compatible = "lowrisc,${inst_type}", "sifive,plic-1.0.0";
%   else:
            compatible = "lowrisc,${inst_type}";
%   endif
            reg = <${"\n                   ".join(["{:#010x} {:#010x}".format(reg.base_addr, reg.size_bytes) for reg in regs])}>;
            reg-names = ${", ".join(["\"{}\"".format(reg_name or inst_type) for reg_name in reg_names])};
%   if inst_name == plic_name:
            interrupt-controller;
            #interrupt-cells = <2>;
            riscv,max-priority = ${"<{}>".format(plic_max_prio)};
            riscv,ndev = ${"<{}>".format(plic_num_irqs)};
            interrupts-extended = ${"<&hlic 11>"};
            interrupt-names = "hart0_external";
%   endif
%   if inst_name in interrupts:
            interrupt-parent = ${"<&{}>".format(plic_name)};
            interrupts = ${", ".join(["<{} 0>".format(irq[1]) for irq in interrupts[inst_name]])};
            interrupt-names = ${", ".join(["\"{}\"".format(irq[0]) for irq in interrupts[inst_name]])};
%   endif
        };
% endfor
    };
};
