# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""This contains a class which is used to help generate `top_{name}.h` and
`top_{name}.h`.
"""
from collections import OrderedDict
from typing import Dict, List, Optional, Tuple

from mako.template import Template

from .lib import get_base_and_size, Name

from reggen.ip_block import IpBlock


class MemoryRegion(object):
    def __init__(self, name: Name, base_addr: int, size_bytes: int):
        assert isinstance(base_addr, int)
        self.name = name
        self.base_addr = base_addr
        self.size_bytes = size_bytes
        self.size_words = (size_bytes + 3) // 4

    def base_addr_name(self):
        return self.name + Name(["base", "addr"])

    def offset_name(self):
        return self.name + Name(["offset"])

    def size_bytes_name(self):
        return self.name + Name(["size", "bytes"])

    def size_words_name(self):
        return self.name + Name(["size", "words"])


class CEnum(object):
    def __init__(self, name):
        self.name = name
        self.enum_counter = 0
        self.finalized = False

        self.constants = []

    def add_constant(self, constant_name, docstring=""):
        assert not self.finalized

        full_name = self.name + constant_name

        value = self.enum_counter
        self.enum_counter += 1

        self.constants.append((full_name, value, docstring))

        return full_name

    def add_last_constant(self, docstring=""):
        assert not self.finalized

        full_name = self.name + Name(["last"])

        _, last_val, _ = self.constants[-1]

        self.constants.append((full_name, last_val, r"\internal " + docstring))
        self.finalized = True

    def render(self):
        template = ("typedef enum ${enum.name.as_snake_case()} {\n"
                    "% for name, value, docstring in enum.constants:\n"
                    "  ${name.as_c_enum()} = ${value}, /**< ${docstring} */\n"
                    "% endfor\n"
                    "} ${enum.name.as_c_type()};")
        return Template(template).render(enum=self)


class CArrayMapping(object):
    def __init__(self, name, output_type_name):
        self.name = name
        self.output_type_name = output_type_name

        self.mapping = OrderedDict()

    def add_entry(self, in_name, out_name):
        self.mapping[in_name] = out_name

    def render_declaration(self):
        template = (
            "extern const ${mapping.output_type_name.as_c_type()}\n"
            "    ${mapping.name.as_snake_case()}[${len(mapping.mapping)}];")
        return Template(template).render(mapping=self)

    def render_definition(self):
        template = (
            "const ${mapping.output_type_name.as_c_type()}\n"
            "    ${mapping.name.as_snake_case()}[${len(mapping.mapping)}] = {\n"
            "% for in_name, out_name in mapping.mapping.items():\n"
            "  [${in_name.as_c_enum()}] = ${out_name.as_c_enum()},\n"
            "% endfor\n"
            "};\n")
        return Template(template).render(mapping=self)


class TopGenC:
    def __init__(self, top_info, name_to_block: Dict[str, IpBlock]):
        self.top = top_info
        self._top_name = Name(["top"]) + Name.from_snake_case(top_info["name"])
        self._name_to_block = name_to_block

        # The .c file needs the .h file's relative path, store it here
        self.header_path = None

        self._init_plic_targets()
        self._init_plic_mapping()
        self._init_alert_mapping()
        self._init_pinmux_mapping()
        self._init_pwrmgr_wakeups()
        self._init_rstmgr_sw_rsts()
        self._init_pwrmgr_reset_requests()
        self._init_clkmgr_clocks()

    def devices(self) -> List[Tuple[Tuple[str, Optional[str]], MemoryRegion]]:
        '''Return a list of MemoryRegion objects for devices on the bus

        The list returned is pairs (full_if, region) where full_if is itself a
        pair (inst_name, if_name). inst_name is the name of some IP block
        instantiation. if_name is the name of the interface (may be None).
        region is a MemoryRegion object representing the device.

        '''
        ret = []  # type: List[Tuple[Tuple[str, Optional[str]], MemoryRegion]]
        for inst in self.top['module']:
            block = self._name_to_block[inst['type']]
            for if_name, rb in block.reg_blocks.items():
                full_if = (inst['name'], if_name)
                full_if_name = Name.from_snake_case(full_if[0])
                if if_name is not None:
                    full_if_name += Name.from_snake_case(if_name)

                name = self._top_name + full_if_name
                base, size = get_base_and_size(self._name_to_block,
                                               inst, if_name)

                region = MemoryRegion(name, base, size)
                ret.append((full_if, region))

        return ret

    def memories(self):
        return [(m["name"],
                 MemoryRegion(self._top_name + Name.from_snake_case(m["name"]),
                              int(m["base_addr"], 0),
                              int(m["size"], 0)))
                for m in self.top["memory"]]

    def _init_plic_targets(self):
        enum = CEnum(self._top_name + Name(["plic", "target"]))

        for core_id in range(int(self.top["num_cores"])):
            enum.add_constant(Name(["ibex", str(core_id)]),
                              docstring="Ibex Core {}".format(core_id))

        enum.add_last_constant("Final PLIC target")

        self.plic_targets = enum

    def _init_plic_mapping(self):
        """We eventually want to generate a mapping from interrupt id to the
        source peripheral.

        In order to do so, we generate two enums (one for interrupts, one for
        sources), and store the generated names in a dictionary that represents
        the mapping.

        PLIC Interrupt ID 0 corresponds to no interrupt, and so no peripheral,
        so we encode that in the enum as "unknown".

        The interrupts have to be added in order, with "none" first, to ensure
        that they get the correct mapping to their PLIC id, which is used for
        addressing the right registers and bits.
        """
        sources = CEnum(self._top_name + Name(["plic", "peripheral"]))
        interrupts = CEnum(self._top_name + Name(["plic", "irq", "id"]))
        plic_mapping = CArrayMapping(
            self._top_name + Name(["plic", "interrupt", "for", "peripheral"]),
            sources.name)

        unknown_source = sources.add_constant(Name(["unknown"]),
                                              docstring="Unknown Peripheral")
        none_irq_id = interrupts.add_constant(Name(["none"]),
                                              docstring="No Interrupt")
        plic_mapping.add_entry(none_irq_id, unknown_source)

        # When we generate the `interrupts` enum, the only info we have about
        # the source is the module name. We'll use `source_name_map` to map a
        # short module name to the full name object used for the enum constant.
        source_name_map = {}

        for name in self.top["interrupt_module"]:
            source_name = sources.add_constant(Name.from_snake_case(name),
                                               docstring=name)
            source_name_map[name] = source_name

        sources.add_last_constant("Final PLIC peripheral")

        for intr in self.top["interrupt"]:
            # Some interrupts are multiple bits wide. Here we deal with that by
            # adding a bit-index suffix
            if "width" in intr and int(intr["width"]) != 1:
                for i in range(int(intr["width"])):
                    name = Name.from_snake_case(intr["name"]) + Name([str(i)])
                    irq_id = interrupts.add_constant(name,
                                                     docstring="{} {}".format(
                                                         intr["name"], i))
                    source_name = source_name_map[intr["module_name"]]
                    plic_mapping.add_entry(irq_id, source_name)
            else:
                name = Name.from_snake_case(intr["name"])
                irq_id = interrupts.add_constant(name, docstring=intr["name"])
                source_name = source_name_map[intr["module_name"]]
                plic_mapping.add_entry(irq_id, source_name)

        interrupts.add_last_constant("The Last Valid Interrupt ID.")

        self.plic_sources = sources
        self.plic_interrupts = interrupts
        self.plic_mapping = plic_mapping

    def _init_alert_mapping(self):
        """We eventually want to generate a mapping from alert id to the source
        peripheral.

        In order to do so, we generate two enums (one for alerts, one for
        sources), and store the generated names in a dictionary that represents
        the mapping.

        Alert Handler has no concept of "no alert", unlike the PLIC.

        The alerts have to be added in order, to ensure that they get the
        correct mapping to their alert id, which is used for addressing the
        right registers and bits.
        """
        sources = CEnum(self._top_name + Name(["alert", "peripheral"]))
        alerts = CEnum(self._top_name + Name(["alert", "id"]))
        alert_mapping = CArrayMapping(
            self._top_name + Name(["alert", "for", "peripheral"]),
            sources.name)

        # When we generate the `alerts` enum, the only info we have about the
        # source is the module name. We'll use `source_name_map` to map a short
        # module name to the full name object used for the enum constant.
        source_name_map = {}

        for name in self.top["alert_module"]:
            source_name = sources.add_constant(Name.from_snake_case(name),
                                               docstring=name)
            source_name_map[name] = source_name

        sources.add_last_constant("Final Alert peripheral")

        for alert in self.top["alert"]:
            if "width" in alert and int(alert["width"]) != 1:
                for i in range(int(alert["width"])):
                    name = Name.from_snake_case(alert["name"]) + Name([str(i)])
                    irq_id = alerts.add_constant(name,
                                                 docstring="{} {}".format(
                                                     alert["name"], i))
                    source_name = source_name_map[alert["module_name"]]
                    alert_mapping.add_entry(irq_id, source_name)
            else:
                name = Name.from_snake_case(alert["name"])
                alert_id = alerts.add_constant(name, docstring=alert["name"])
                source_name = source_name_map[alert["module_name"]]
                alert_mapping.add_entry(alert_id, source_name)

        alerts.add_last_constant("The Last Valid Alert ID.")

        self.alert_sources = sources
        self.alert_alerts = alerts
        self.alert_mapping = alert_mapping

    def _init_pinmux_mapping(self):
        """Generate C enums for addressing pinmux registers and in/out selects.

        Inputs/outputs are connected in the order the modules are listed in
        the hjson under the "mio_modules" key. For each module, the corresponding
        inouts are connected first, followed by either the inputs or the outputs.

        Inputs:
        - Peripheral chooses register field (pinmux_peripheral_in)
        - Insel chooses MIO input (pinmux_insel)

        Outputs:
        - MIO chooses register field (pinmux_mio_out)
        - Outsel chooses peripheral output (pinmux_outsel)

        Insel and outsel have some special values which are captured here too.
        """
        pinmux_info = self.top['pinmux']
        pinout_info = self.top['pinout']

        # Peripheral Inputs
        peripheral_in = CEnum(self._top_name +
                              Name(['pinmux', 'peripheral', 'in']))
        i = 0
        for sig in pinmux_info['ios']:
            if sig['connection'] == 'muxed' and sig['type'] in ['inout', 'input']:
                index = Name([str(sig['idx'])]) if sig['idx'] != -1 else Name([])
                name = Name.from_snake_case(sig['name']) + index
                peripheral_in.add_constant(name, docstring='Peripheral Input {}'.format(i))
                i += 1

        peripheral_in.add_last_constant('Last valid peripheral input')

        # Pinmux Input Selects
        insel = CEnum(self._top_name + Name(['pinmux', 'insel']))
        insel.add_constant(Name(['constant', 'zero']),
                           docstring='Tie constantly to zero')
        insel.add_constant(Name(['constant', 'one']),
                           docstring='Tie constantly to one')
        i = 0
        for pad in pinout_info['pads']:
            if pad['connection'] == 'muxed':
                insel.add_constant(Name([pad['name']]),
                                   docstring='MIO Pad {}'.format(i))
                i += 1
        insel.add_last_constant('Last valid insel value')

        # MIO Outputs
        mio_out = CEnum(self._top_name + Name(['pinmux', 'mio', 'out']))
        i = 0
        for pad in pinout_info['pads']:
            if pad['connection'] == 'muxed':
                mio_out.add_constant(Name.from_snake_case(pad['name']),
                                     docstring='MIO Pad {}'.format(i))
                i += 1
        mio_out.add_last_constant('Last valid mio output')

        # Pinmux Output Selects
        outsel = CEnum(self._top_name + Name(['pinmux', 'outsel']))
        outsel.add_constant(Name(['constant', 'zero']),
                            docstring='Tie constantly to zero')
        outsel.add_constant(Name(['constant', 'one']),
                            docstring='Tie constantly to one')
        outsel.add_constant(Name(['constant', 'high', 'z']),
                            docstring='Tie constantly to high-Z')
        i = 0
        for sig in pinmux_info['ios']:
            if sig['connection'] == 'muxed' and sig['type'] in ['inout', 'output']:
                index = Name([str(sig['idx'])]) if sig['idx'] != -1 else Name([])
                name = Name.from_snake_case(sig['name']) + index
                outsel.add_constant(name, docstring='Peripheral Output {}'.format(i))
                i += 1

        outsel.add_last_constant('Last valid outsel value')

        self.pinmux_peripheral_in = peripheral_in
        self.pinmux_insel = insel
        self.pinmux_mio_out = mio_out
        self.pinmux_outsel = outsel

    def _init_pwrmgr_wakeups(self):
        enum = CEnum(self._top_name +
                     Name(["power", "manager", "wake", "ups"]))

        for signal in self.top["wakeups"]:
            enum.add_constant(
                Name.from_snake_case(signal["module"]) +
                Name.from_snake_case(signal["name"]))

        enum.add_last_constant("Last valid pwrmgr wakeup signal")

        self.pwrmgr_wakeups = enum

    # Enumerates the positions of all software controllable resets
    def _init_rstmgr_sw_rsts(self):
        sw_rsts = [
            rst for rst in self.top["resets"]["nodes"]
            if 'sw' in rst and rst['sw'] == 1
        ]

        enum = CEnum(self._top_name +
                     Name(["reset", "manager", "sw", "resets"]))

        for rst in sw_rsts:
            enum.add_constant(Name.from_snake_case(rst["name"]))

        enum.add_last_constant("Last valid rstmgr software reset request")

        self.rstmgr_sw_rsts = enum

    def _init_pwrmgr_reset_requests(self):
        enum = CEnum(self._top_name +
                     Name(["power", "manager", "reset", "requests"]))

        for signal in self.top["reset_requests"]:
            enum.add_constant(
                Name.from_snake_case(signal["module"]) +
                Name.from_snake_case(signal["name"]))

        enum.add_last_constant("Last valid pwrmgr reset_request signal")

        self.pwrmgr_reset_requests = enum

    def _init_clkmgr_clocks(self):
        """
        Creates CEnums for accessing the software-controlled clocks in the
        design.

        The logic here matches the logic in topgen.py in how it instantiates the
        clock manager with the described clocks.

        We differentiate "gateable" clocks and "hintable" clocks because the
        clock manager has separate register interfaces for each group.
        """

        aon_clocks = set()
        for src in self.top['clocks']['srcs'] + self.top['clocks'][
                'derived_srcs']:
            if src['aon'] == 'yes':
                aon_clocks.add(src['name'])

        gateable_clocks = CEnum(self._top_name + Name(["gateable", "clocks"]))
        hintable_clocks = CEnum(self._top_name + Name(["hintable", "clocks"]))

        # This replicates the behaviour in `topgen.py` in deriving `hints` and
        # `sw_clocks`.
        for group in self.top['clocks']['groups']:
            for (name, source) in group['clocks'].items():
                if source not in aon_clocks:
                    # All these clocks start with `clk_` which is redundant.
                    clock_name = Name.from_snake_case(name).remove_part("clk")
                    docstring = "Clock {} in group {}".format(
                        name, group['name'])
                    if group["sw_cg"] == "yes":
                        gateable_clocks.add_constant(clock_name, docstring)
                    elif group["sw_cg"] == "hint":
                        hintable_clocks.add_constant(clock_name, docstring)

        gateable_clocks.add_last_constant("Last Valid Gateable Clock")
        hintable_clocks.add_last_constant("Last Valid Hintable Clock")

        self.clkmgr_gateable_clocks = gateable_clocks
        self.clkmgr_hintable_clocks = hintable_clocks
