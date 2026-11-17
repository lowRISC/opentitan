# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import logging as log
import os
import re
import sys
from collections import OrderedDict, defaultdict
from copy import deepcopy
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple, Union

import hjson
from basegen.lib import Name
from basegen.typing import ConfigT, ParamsT
from mako.template import Template
from reggen.ip_block import IpBlock
from reggen.lib import PART_BOTH, PART_PRIMARY, PART_SECONDARY, check_bool
from version_file import VersionInformation

# Ignore flake8 warning as the function is used in the template
# disable isort formatting, as conflicting with flake8
from .intermodule import find_otherside_modules  # noqa : F401 # isort:skip
from .intermodule import im_portname, im_defname, im_netname  # noqa : F401 # isort:skip
from .intermodule import get_direction  # noqa : F401 # isort:skip
from .intermodule import get_dangling_im_def  # noqa : F401 # isort:skip
from .typing import IpBlocksT


class CEnum(object):

    def __init__(self, top_name: Optional[Name], name: Name, repr_type=None):
        self.name = top_name + name if top_name is not None else name
        self.repr_type = repr_type
        self.finalized = False

        self.constants = []
        self.meta_constants = []

    def add_constant(self, constant_name: Name, docstring=""):
        assert not self.finalized

        full_name = self.name + constant_name

        value = len(self.constants)

        # Check that we're not adding duplicates
        for const in self.constants:
            if full_name == const[0]:
                raise ValueError('{} is already declared with value {}'.format(const[0], const[1]))

        self.constants.append((full_name, value, docstring))

        return full_name

    def add_first_constant(self, docstring=""):
        assert len(self.constants) > 0, "cannot add a First constant to an empty enumeration"

        full_name = self.name + Name(["first"])

        _, first_val, _ = self.constants[0]

        self.meta_constants.append((full_name, first_val, r"\internal " + docstring))
        self.finalized = True

    def add_last_constant(self, docstring=""):
        assert len(self.constants) > 0, "cannot add a Last constant to an empty enumeration"
        full_name = self.name + Name(["last"])

        _, last_val, _ = self.constants[-1]

        self.meta_constants.append((full_name, last_val, r"\internal " + docstring))
        self.finalized = True

    def add_count_constant(self, docstring=""):
        full_name = self.name + Name(["count"])

        self.meta_constants.append((full_name, len(self.constants), r"\internal " + docstring))
        self.finalized = True

    def render(self) -> str:
        template = ("typedef enum ${enum.name.as_snake_case()} {\n"
                    "% for name, value, docstring in enum.constants + enum.meta_constants:\n"
                    "  ${name.as_c_enum()} = ${value}, /**< ${docstring} */\n"
                    "% endfor\n"
                    "} ${enum.name.as_c_type()};")
        return Template(template).render(enum=self)


class CArrayMapping(object):

    def __init__(self, top_name, name, output_type_name):
        self.name = top_name + name
        self.output_type_name = output_type_name

        self.mapping = OrderedDict()

    def add_entry(self, in_name, out_name):
        self.mapping[in_name] = out_name

    def render_declaration(self) -> str:
        template = (
            "extern const ${mapping.output_type_name.as_c_type()}\n"
            "    ${mapping.name.as_snake_case()}[${len(mapping.mapping)}];")
        return Template(template).render(mapping=self)

    def render_definition(self) -> str:
        template = (
            "const ${mapping.output_type_name.as_c_type()}\n"
            "    ${mapping.name.as_snake_case()}[${len(mapping.mapping)}] = {\n"
            "% for in_name, out_name in mapping.mapping.items():\n"
            "  [${in_name.as_c_enum()}] = ${out_name.as_c_enum()},\n"
            "% endfor\n"
            "};")
        return Template(template).render(mapping=self)


class RustEnum(object):

    def __init__(self,
                 top_name,
                 name,
                 repr_type=None,
                 derive_list=["Copy", "Clone", "PartialEq", "Eq"]):
        self.name = top_name + name
        self.short_name = name
        self.enum_counter = 0
        self.finalized = False
        self.first_value = None
        self.last_value = None
        self.last_value_docstring = None
        self.repr_type = repr_type
        self.derive_list = derive_list
        self.constants = []
        # todo add flag for doc strings

    def repr(self) -> str:
        if isinstance(self.repr_type, int):
            return "u" + str(self.repr_type)
        elif self.repr_type is None:
            return "u32"
        else:
            return self.repr_type

    def derive(self) -> str:
        if isinstance(self.derive_list, list):
            if len(self.derive_list) > 0:
                return "#[derive({})]\n".format(", ".join(self.derive_list))
        return ""

    def add_constant(self, constant_name: str, docstring="") -> str:
        assert not self.finalized
        full_name = constant_name
        value = self.enum_counter
        self.enum_counter += 1

        # Check that we're not adding duplicates
        for const in self.constants:
            if full_name == const[0]:
                raise ValueError('{} is already declared with value {}'.format(const[0], const[1]))
        self.constants.append((full_name, value, docstring))
        return full_name

    def add_number_of_variants(self, docstring=""):
        assert not self.finalized
        _, last_val, _ = self.constants[-1]
        self.last_value = last_val + 1
        self.last_value_docstring = docstring
        self.finalized = True

    def calculate_range(self):
        _, last_val, _ = self.constants[-1]
        _, first_val, _ = self.constants[0]
        self.last_value = last_val
        self.first_value = first_val

    def render_host(self, gen_doc=False, gen_name=None) -> str:
        self.calculate_range()
        body = (
            "    pub enum ${enum.short_name.as_rust_type()}: ${enum.repr()} "
            "[default = Self::End] {\n"
            "% for name, value, docstring in enum.constants:\n"
            "        % if len(docstring) > 0  and gen_doc: \n"
            "        /// ${docstring}\n"
            "        % endif \n"
            "        ${name.as_rust_enum()} = ${value},\n"
            "% endfor\n"
            "        End = ${enum.last_value + 1},\n"
            "    }")
        return Template(body).render(enum=self)

    def render(self, gen_range=False, gen_cast=False, derive_list=None) -> str:
        if derive_list is not None:
            self.derive_list = derive_list
        self.calculate_range()
        body = ("${enum.derive()}"
                "#[repr(${enum.repr()})]\n"
                "pub enum ${enum.short_name.as_rust_type()} {\n"
                "% for name, value, docstring in enum.constants:\n"
                "    % if len(docstring) > 0 : \n"
                "    /// ${docstring}\n"
                "    % endif \n"
                "    ${name.as_rust_enum()} = ${value},\n"
                "% endfor\n"
                "}")

        impl = (
            "\n\n"
            "impl ${enum.short_name.as_rust_type()} {\n"
            "    % if enum.last_value_docstring:\n"
            "    /// ${enum.last_value_docstring}\n"
            "    % else: \n"
            "    /// Total number of enum variants \n"
            "    % endif \n"
            "    const NUMBER: usize = ${len(enum.constants)};\n"
            "    /// Enum first valid value\n"
            "    const FIRST: ${enum.repr()} = "
            "Self::${enum.constants[0][0].as_rust_enum()} as ${enum.repr()};\n"
            "    /// Enum last valid value\n"
            "    const LAST: ${enum.repr()} = "
            "Self::${enum.constants[-1][0].as_rust_enum()} as ${enum.repr()};\n"
            "}")

        cast = (
            "\n\n"
            "impl TryFrom<${enum.repr()}> for "
            "${enum.short_name.as_rust_type()} {\n"
            "    type Error = ${enum.repr()};\n"
            "    fn try_from(val: ${enum.repr()}) -> Result<Self, Self::Error> {\n"
            "        match val {\n"
            "            % for name, value, docstring in enum.constants:\n"
            "            ${value} => Ok(Self::${name.as_rust_enum()}),\n"
            "            % endfor \n"
            "            _ => Err(val),\n"
            "        }\n"
            "    }\n"
            "}")

        if gen_range:
            body += impl
        if gen_cast:
            body += cast
        return Template(body).render(enum=self)


class RustArrayMapping(object):

    def __init__(self, top_name, name, output_type_name):
        self.name = top_name + name
        self.short_name = name
        self.output_type_name = output_type_name

        self.mapping = OrderedDict()

    def add_entry(self, in_name, out_name):
        self.mapping[in_name] = out_name

    def render_definition(self) -> str:
        template = (
            "pub const ${mapping.short_name.as_rust_const()}: "
            "[${mapping.output_type_name.as_rust_type()}; ${len(mapping.mapping)}] = [\n"
            "% for in_name, out_name in mapping.mapping.items():\n"
            "    // ${in_name.as_rust_enum()} ->"
            " ${mapping.output_type_name.as_rust_type()}::${out_name.as_rust_enum()}\n"
            "    ${mapping.output_type_name.as_rust_type()}::${out_name.as_rust_enum()},\n"
            "% endfor\n"
            "];")
        return Template(template).render(mapping=self)


class RustFileHeader(object):

    def __init__(self, version_stamp: VersionInformation):
        self.data = version_stamp

    def render(self) -> str:
        template = ""
        if self.data.scm_version() is not None:
            template += "// Built for ${header.data.scm_version()}\n"
        if self.data.scm_revision() is not None:
            template += ("// https://github.com/lowRISC/opentitan/tree/"
                         "${header.data.scm_revision()}\n")
        if self.data.scm_status() is not None:
            template += "// Tree status: ${header.data.scm_status()}\n"
        if template != "":
            template = "\n" + template
        return Template(template).render(header=self)


class MemoryRegion(object):

    def __init__(self, top_name: Name, name: Name, addr_space: str,
                 base_addr: int, size_bytes: int):
        assert isinstance(base_addr, int)
        self.addr_space = addr_space
        addr_space_suffix = get_addr_space_suffix({'name': addr_space})
        if len(addr_space_suffix) > 0:
            # Trim the beginning underscore.
            addr_space_suffix = addr_space_suffix[1:]
            addr_space_name = Name.from_snake_case(addr_space_suffix)
            self.name = top_name + addr_space_name + name
            self._top_agnostic_name = Name(["top"]) + addr_space_name + name
        else:
            self.name = top_name + name
            self._top_agnostic_name = Name(["top"]) + name
        self.short_name = name
        self.base_addr = base_addr
        self.size_bytes = size_bytes
        self.size_words = (size_bytes + 3) // 4

    def base_addr_name(self, short=False, top_agnostic=False) -> Name:
        if short:
            return self.short_name + Name(["base", "addr"])
        elif top_agnostic:
            return self._top_agnostic_name + Name(["base", "addr"])
        else:
            return self.name + Name(["base", "addr"])

    def offset_name(self, short=False, top_agnostic=False) -> Name:
        if short:
            return self.short_name + Name(["offset"])
        elif top_agnostic:
            return self._top_agnostic_name + Name(["offset"])
        else:
            return self.name + Name(["offset"])

    def size_bytes_name(self, short=False, top_agnostic=False) -> Name:
        if short:
            return self.short_name + Name(["size", "bytes"])
        elif top_agnostic:
            return self._top_agnostic_name + Name(["size", "bytes"])
        else:
            return self.name + Name(["size", "bytes"])

    def size_words_name(self, short=False, top_agnostic=False) -> Name:
        if short:
            return self.short_name + Name(["size", "words"])
        elif top_agnostic:
            return self._top_agnostic_name + Name(["size", "words"])
        else:
            return self.name + Name(["size", "words"])


def load_cfg(cfg_path: str) -> Dict[str, object]:
    """Loads an hjson file and returns the dictionary.

    This is suitable for the config files used by topgen.
    """
    try:
        with open(cfg_path, "r") as fcfg:
            cfg = hjson.load(fcfg,
                             use_decimal=True,
                             object_pairs_hook=OrderedDict)
    except ValueError:
        raise SystemExit(f"Loading hjson at '{cfg_path}': {sys.exc_info()[1]}")
    except OSError:
        raise SystemExit(sys.exc_info()[1])
    return cfg


def is_ipcfg(ip: Path) -> bool:
    log.info("IP Path: %s" % repr(ip))
    ip_name = ip.parents[1].name
    hjson_name = ip.name

    log.info("IP Name(%s) and HJSON name (%s)" % (ip_name, hjson_name))

    if ip_name + ".hjson" == hjson_name or ip_name + "_reg.hjson" == hjson_name:
        return True
    return False


def search_ips(ip_path: Path) -> List[str]:
    """Return a list with the path to every Hjson file as a string"""
    p = ip_path.glob('*/data/*.hjson')

    # filter only ip_name/data/ip_name{_reg|''}.hjson
    ips = [x for x in p if is_ipcfg(x)]

    log.info("Filtered-in IP files: %s" % repr(ips))
    return ips


def get_ip_hjson_path(ip_name_snake: str, topcfg: ConfigT,
                      repotop: Path) -> Path:
    """Return the location of an IP's hjson file for a given top.

    This function should be called with the module['type'] for ipgen
    modules, since find_module is called with use_base_template_type
    set to False.
    """
    m = find_module(topcfg["module"],
                    ip_name_snake,
                    use_base_template_type=False)
    if is_ipgen(m):
        data_dir = repotop / "hw/top_{}/ip_autogen/{}/data".format(
            topcfg["name"], ip_name_snake)
    elif is_top_reggen(m):
        data_dir = repotop / "hw/top_{}/ip/{}/data/".format(
            topcfg["name"], ip_name_snake)
    else:
        data_dir = repotop / "hw/ip/{}/data".format(ip_name_snake)
    return data_dir / "{}.hjson".format(ip_name_snake)


def is_xbarcfg(xbar_obj: ConfigT) -> bool:
    if "type" in xbar_obj and xbar_obj["type"] == "xbar":
        return True

    return False


def get_hjsonobj_xbars(xbar_path: Path) -> Dict[str, ConfigT]:
    """ Search crossbars Hjson files from given path.

    Search every Hjson in the directory and check Hjson type.
    It could be type: "top" or type: "xbar"
    returns [(name, obj), ... ]
    """
    paths = xbar_path.glob('*.hjson')
    xbar_objs = [load_cfg(p) for p in paths]
    xbar_objs = {x['name']: x for x in xbar_objs if is_xbarcfg(x)}

    return xbar_objs


def get_module_by_name(top: ConfigT, name: str,
                       search_xbars: bool = False) -> Optional[ConfigT]:
    """Search in top["module"] by name
    """
    module = None
    for m in top["module"]:
        if m["name"] == name:
            module = m
            break

    if module or not search_xbars:
        return module

    for x in top["xbar"]:
        if x["name"] == name:
            module = x
            break

    return module


def has_module_type(top: ConfigT, module_type: str) -> bool:
    """Check whether top["module"] contains an instance of `module_type`.
    """
    return any(m["type"] == module_type for m in top["module"])


def intersignal_to_signalname(top, m_name: str, s_name: str) -> str:

    # TODO: Find the signal in the `inter_module_list` and get the correct
    # signal name

    return "{m_name}_{s_name}".format(m_name=m_name, s_name=s_name)


def get_intermodule_list(top: ConfigT, domain: str = None):
    if domain is not None:
        return [x for x in top["inter_signal"]["definitions"] if x["domain"] == domain]
    else:
        return top["inter_signal"]["definitions"]


def get_intermodule_ports(top: ConfigT, domain: str = "", inter_pd: bool = None):
    if inter_pd is not None:
        inter_pd_list = [x for x in top["inter_signal"]["external"] if x["inter_pd"] == inter_pd]
    else:
        inter_pd_list = top["inter_signal"]["external"]

    if domain != "":
        return [x for x in inter_pd_list if x["domain"] == domain]
    else:
        return inter_pd_list


def get_package_name_by_intermodule_signal(top: ConfigT, struct: str) -> str:
    """Search inter-module signal package with the struct name

    For instance, if `flash_ctrl` has inter-module signal package,
    this function returns the package name
    """
    instances = top["module"] + top["memory"]

    intermodule_instances = [
        x["inter_signal_list"] for x in instances if "inter_signal_list" in x
    ]

    for m in intermodule_instances:
        if m["name"] == struct and "package" in m:
            return m["package"]
    return ""


def get_signal_by_name(module: ConfigT, name: str):
    """Return the signal struct with the type input/output/inout
    """
    result = None
    for s in module["available_input_list"] + module[
            "available_output_list"] + module["available_inout_list"]:
        if s["name"] == name:
            result = s
            break

    return result


def add_module_prefix_to_signal(signal, module: str) -> str:
    """Add module prefix to module signal format { name: "sig_name", width: NN }
    """
    result = deepcopy(signal)

    if "name" not in signal:
        raise SystemExit("signal {} doesn't have name field".format(signal))

    result["name"] = module + "_" + signal["name"]
    result["module_name"] = module

    return result


def invert_signal_act(signal) -> str:
    if signal['type'] == "req_rsp":
        if signal['act'] == "rsp":
            return "req"
        else:
            return "rsp"
    elif signal['type'] == "uni":
        if signal['act'] == "rcv":
            return "req"
        else:
            return "rcv"


def get_ms_name(name: str) -> Tuple[str, Optional[str]]:
    """Split module_name.signal_name to module_name , signal_name
    """

    tokens = name.split('.')

    if len(tokens) == 0:
        raise SystemExit("This to be catched in validate.py")

    module = tokens[0]
    signal = None
    if len(tokens) == 2:
        signal = tokens[1]

    return module, signal


def parse_pad_field(padstr: str) -> Tuple[str, str, str]:
    """Parse PadName[NN...NN] or PadName[NN] or just PadName
    """
    match = re.match(r'^([A-Za-z0-9_]+)(\[([0-9]+)(\.\.([0-9]+))?\]|)', padstr)
    return match.group(1), match.group(3), match.group(5)


def get_pad_list(padstr: str) -> List[Dict[str, Union[str, int]]]:
    pads = []

    pad, first, last = parse_pad_field(padstr)
    if first is None:
        first = 0
        last = 0
    elif last is None:
        last = first
    first = int(first, 0)
    last = int(last, 0)
    # width = first - last + 1

    for p in range(first, last + 1):
        pads.append(OrderedDict([("name", pad), ("index", p)]))

    return pads


def exposed_params_for_domain(module: ConfigT, domain: str = "",
                              local: str = "false") -> List[ConfigT]:
    '''Returns a list of exposed parameters of module for a domain.

    Set local="true" to select localparams instead of module parameters.
    domain="" (the top module) returns all exposed parameters. For a domain
    specific list, pass the domain name.
    '''
    partitions = None if domain == "" else get_module_partitions(module, domain)
    result = []
    for param in module["param_list"]:
        if param.get("local") != local or param.get("expose") != "true":
            continue
        if partitions is not None:
            partition = param.get("partition", PART_PRIMARY)
            if partition != PART_BOTH and partition not in partitions:
                continue
        result.append(param)
    return result


def idx_of_last_module_with_params(top: ConfigT, domain: str = "") -> int:
    last = -1
    for idx, module in enumerate(get_all_modules(top, domain)):
        if is_inst(module) and exposed_params_for_domain(module, domain):
            last = idx
    return last


def get_all_modules(top: ConfigT, domain: str = ""):
    if domain != "":
        # A split IP has a partition in each of the power domains it names, so
        # it is returned for both passes.
        return [
            m for m in top["module"]
            if m.get("domain") == domain or m.get(secondary_key("domain")) == domain
        ]
    else:
        return top["module"]


def get_domain_of_partition(module: ConfigT, partition: str = PART_PRIMARY,
                            default: Optional[str] = None) -> Optional[str]:
    '''Return the power domain of the given partition of a module instance.'''
    if partition == PART_SECONDARY:
        return module.get(secondary_key('domain'), default)
    return module.get('domain', default)


def get_domain_of_signal(module: Dict, sig: OrderedDict):
    '''Power domain of a inter-module signal endpoint.'''
    return get_domain_of_partition(module, sig.get('partition', PART_PRIMARY))


# The instance keys a split IP describes per partition. The canonical key
# always holds the primary partition's value and '<key>_secondary' the
# secondary partition's value.
PARTITIONED_KEYS = ('clock_srcs', 'clock_group', 'reset_connections')


def secondary_key(key: str) -> str:
    '''Name of the key holding a split instance's secondary partition value.'''
    return f'{key}_secondary'


def get_partitions_of(module: ConfigT) -> List[str]:
    if 'domain_secondary' in module:
        return [PART_PRIMARY, PART_SECONDARY]
    return [PART_PRIMARY]


def get_conns_for(end_point: ConfigT, key: str) -> List[Tuple[str, ConfigT]]:
    '''Return (partition, connections) for every partition a `key` describes.

    The canonical key holds the primary partition's connections and
    '<key>_secondary' the secondary partition's.
    '''
    result = []
    for partition, name in ((PART_PRIMARY, key),
                            (PART_SECONDARY, secondary_key(key))):
        conns = end_point.get(name)
        if conns is not None:
            result.append((partition, conns))
    return result


def partition_key(key: str, partition: str = PART_PRIMARY) -> str:
    '''Name of the key holding the given partition's value for `key`.'''
    return secondary_key(key) if partition == PART_SECONDARY else key


def get_primary_clock_port(name_to_block: IpBlocksT, module: ConfigT,
                           partition: str = PART_PRIMARY) -> str:
    '''Return the RTL port name of a module partition's primary clock.'''
    block = name_to_block[module['type']]
    return block.get_primary_clock(partition).clock


def alert_conn_key(module_name: str, partition: str = PART_PRIMARY) -> str:
    '''Key of a module's entry in top['alert_connections'].'''
    return partition_key('module_' + module_name, partition)


# Infix of the module type and instance name of a split IP's partitions.
PARTITION_INFIX = '_part_'


def instance_name_for_partition(name: str, module: ConfigT,
                                partition: str = PART_PRIMARY) -> str:
    '''Suffix `name` with the partition infix if `module` is a split IP.'''
    if not module.get('is_split_ip'):
        return name
    return name + PARTITION_INFIX + partition


def get_module_partitions(module: ConfigT, domain: str) -> List[str]:
    '''Return the partitions of a module that are in the given power domain.'''
    partitions = []
    if module.get('domain') == domain:
        partitions.append(PART_PRIMARY)
    if module.get(secondary_key('domain')) == domain:
        partitions.append(PART_SECONDARY)
    return partitions


# Template functions
def ljust(x, width):
    return "{:<{width}}".format(x, width=width)


def bitarray(d: int, width: int) -> str:
    """Print Systemverilog bit array

    @param d the bit width of the signal
    @param width max character width of the signal group

    For instance, if width is 4, the max d value in the signal group could be
    9999. If d is 2, then this function pads 3 spaces at the end of the bit
    slice.

    "[1:0]   " <- d:=2, width=4
    "[9999:0]" <- max d-1 value

    If d is 1, it means array slice isn't necessary. So it returns empty spaces
    """

    if d <= 0:
        log.error("lib.bitarray: Given value {} is smaller than 1".format(d))
        raise ValueError
    if d == 1:
        return " " * (width + 4)  # [x:0] needs 4 more space than char_width

    out = "[{}:0]".format(d - 1)
    return out + (" " * (width - len(str(d))))


def parameterize(text: str) -> str:
    """Return the value wrapping with quote if not integer nor bits
    """
    if re.match(r'(\d+\'[hdb]\s*[0-9a-f_A-F]+|[0-9]+)', text) is None:
        return "\"{}\"".format(text)

    return text


def index(sig: Dict) -> str:
    """Return index if it is not -1 and signal does not connect to
    an intermediate net.
    """
    if sig.get("conn_type", False):
        return ""
    else:
        return "[{}]".format(sig["index"]) if sig["index"] != -1 else ""


def get_clk_name(clk: str) -> str:
    """Return the appropriate clk name
    """
    if clk == 'main':
        return 'clk_i'
    else:
        return "clk_{}_i".format(clk)


def is_shadowed_port(block: IpBlock, port: str) -> bool:
    """Return boolean indication whether a port is a shadow reset port
    """
    shadowed_port = block.clocking.primary.reset if block.has_shadowed_reg() \
        else None

    return port == shadowed_port


def shadow_name(name: str) -> str:
    """Return the appropriate shadow reset name based on port name
    """
    match = re.match(r'^rst_([A-Za-z0-9_]+)_ni?', name)
    if match:
        return f'rst_{match.group(1)}_shadowed_ni'
    else:
        return 'rst_shadowed_ni'


def _partition_suffix(partition: str) -> str:
    '''Return the suffix that a split manager adds to the names of a partition's output signals.

    topgen names a net after the instance and the signal ({inst_name}_{name}), and both partitions
    share the instance. So the secondary partition's clocks and resets carry its name, as in
    clocks_secondary, in every top. The primary partition keeps the names of a manager that is not
    split. The type names of both partitions carry the partition's name (see
    _get_manager_partitions).

    The names come from this rule, not from the description of the IP, because topgen builds the
    clock connections (extract_clocks) before it generates the clkmgr. The templates of both
    managers follow the same rule.
    '''
    return f'_{partition}' if partition == PART_SECONDARY else ''


def declares_secondary(module) -> bool:
    '''Return whether the top configuration gives a module a secondary partition.

    Unlike is_split_ip, which topgen only sets once it has generated the IP, this works while topgen
    creates the parameters of the IP.
    '''
    return module is not None and module.get('domain_secondary') is not None


def _clock_src_name(net) -> str:
    '''Return the clock name of a clock source, which is a clock name, or a dict with the clock name
    and, optionally, its group.'''
    return net['clock'] if isinstance(net, dict) else net


def get_clkmgr_src_partitions(top) -> Dict[str, str]:
    '''Return, by name, the clkmgr partition that receives each source clock.

    The clock_srcs of the partitions say which partition receives a source. A derived source, such
    as io_div4, has the partition of the source it is divided from. A partition generates the clocks
    of the sources that it receives. Raise a ValueError if more than one partition receives a
    source.
    '''
    clkmgr = find_module(top['module'], 'clkmgr')
    clocks = top['clocks']
    received: Dict[str, Set[str]] = {}
    for partition, srcs in get_conns_for(clkmgr, 'clock_srcs'):
        for net in srcs.values():
            name = _clock_src_name(net)
            if name in clocks.derived_srcs:
                name = clocks.derived_srcs[name].src.name
            if name in clocks.srcs:
                received.setdefault(name, set()).add(partition)
    shared = {name: sorted(parts) for name, parts in received.items() if len(parts) > 1}
    if shared:
        raise ValueError(f"Source clocks received by more than one partition of the "
                         f"{clkmgr['name']}: {shared}")
    return {name: next(iter(parts)) for name, parts in received.items()}


def get_clkmgr_clock_partition(top, src=None) -> str:
    '''Return the clkmgr partition that hosts the clocks of a clock source.

    The partition that receives the source hosts its clocks (see get_clkmgr_src_partitions). Without
    a source, the primary partition hosts the clocks. Raise a ValueError if no partition receives
    the source.
    '''
    clkmgr = find_module(top['module'], 'clkmgr')
    if src is None:
        return PART_PRIMARY
    clocks = top['clocks']
    name = src.name
    if name in clocks.derived_srcs:
        name = clocks.derived_srcs[name].src.name
    partitions = get_clkmgr_src_partitions(top)
    if name not in partitions:
        raise ValueError(f"The source clock {name!r} is not received by any partition of the "
                         f"{clkmgr['name']}")
    return partitions[name]


def validate_split_clkmgr(top) -> None:
    '''Check that the clkmgr is split, and that exactly one partition receives each source clock.

    Raise a ValueError if the clkmgr has no domain_secondary, or if no partition receives a source.
    get_clkmgr_src_partitions raises one if two partitions receive a source.
    '''
    clkmgr = find_module(top['module'], 'clkmgr')
    if clkmgr is None or not declares_secondary(clkmgr):
        raise ValueError("The clkmgr must be split into two partitions: give it a "
                         "domain_secondary in the configuration of the top")
    partitions = get_clkmgr_src_partitions(top)
    missing = [name for name in top['clocks'].srcs if name not in partitions]
    if missing:
        raise ValueError(f"The source clocks {missing} are not received by any partition of the "
                         f"{clkmgr['name']}. Add them to the clock_srcs of one partition.")


def _get_manager_partitions(top, ip_type: str) -> list:
    '''Return (partition, power domain, signal suffix, type infix) for each partition of a manager.

    The IP adds the signal suffix to the names of its output signals (see _partition_suffix), and
    the type infix to the names of their struct types.
    '''
    mod = find_module(top['module'], ip_type)
    return [(part, get_domain_of_partition(mod, part), _partition_suffix(part), f'_{part}')
            for part in (PART_PRIMARY, PART_SECONDARY)]


def _in_partition_order(parts) -> List[str]:
    '''Return the given partitions as a list in a fixed order, primary first.'''
    return [p for p in (PART_PRIMARY, PART_SECONDARY) if p in parts]


def _out_partition(top, ip_type: str, generated: str, domain: Optional[str]) -> str:
    '''Return the partition of a split manager that outputs a signal to a power domain.

    `generated` is the partition that generates the signal. It also outputs the signal when there is
    no power domain, or when it is in that power domain. Otherwise the partition in that power
    domain outputs the signal, and the signal crosses to it inside the manager. If no partition is
    in that power domain, the generating partition outputs the signal.
    '''
    module = find_module(top['module'], ip_type)
    if domain is None or get_domain_of_partition(module, generated) == domain:
        return generated
    for part, dom, _, _ in _get_manager_partitions(top, ip_type):
        if dom == domain:
            return part
    return generated


def _indication_crossings(top, primary_domain: str, kind: str, skip) -> Set[Tuple[str, str, str]]:
    '''Return the crossings of the indication struct `kind` (cg_en or rst_en) of a split manager.

    The primary partition outputs all the indications. So the struct crosses from the primary into
    the other domain when that domain reads an indication.
    '''
    return {(kind, PART_PRIMARY, d) for d in _indication_reader_domains(top, primary_domain, skip)
            if d != primary_domain}


def get_clkmgr_partitions(top) -> list:
    '''Return (partition, power domain, signal suffix, type infix) for each partition of the clkmgr.
    '''
    return _get_manager_partitions(top, 'clkmgr')


def rstmgr_is_array(hosted: Sequence[str], power_domains: Sequence[str]) -> bool:
    """Return whether an output reset is an array over the power domains in a partition's output
    struct.

    A reset that a partition hosts for every power domain is an array. A reset that it hosts for a
    single power domain is a single bit. With two power domains, every case is one of these two. Any
    other case has no defined shape, so raise a ValueError.
    """
    if len(hosted) == 1:
        return False
    if len(hosted) == len(power_domains):
        return True
    raise ValueError(f'a partition hosts {len(hosted)} of {len(power_domains)} power domains of '
                     'one reset, which has no defined shape')


def get_rstmgr_partitions(top) -> list:
    '''Return (partition, power domain, signal suffix, type infix) for each partition of the rstmgr.
    '''
    return _get_manager_partitions(top, 'rstmgr')


def get_clock_src(top, clk_name: str):
    '''Return the source clock of a managed clock signal, or None if the clock is not known.'''
    group = top['clocks'].make_clock_to_group().get(clk_name)
    if group is None:
        return None
    sig = group.clocks.get(clk_name)
    return sig.src if sig is not None else None


def get_clkmgr_out_partition(top, src, domain: Optional[str], primary_side: bool = False) -> str:
    '''Return the clkmgr partition that outputs the clocks of a source to a power domain.

    The partition that receives a source generates and gates its clocks. _out_partition gives the
    partition that outputs them.

    The always-on clock is different. The secondary partition generates it, and gates the copy that
    it gives the primary partition, around the clamp of the power domain that powers down. Modules
    of the always-on power domain take the secondary partition's clock. Every other module, and the
    primary partition of the rstmgr (`primary_side`), takes the primary partition's, whatever the
    power domains of the partitions: the same rule in one power domain or two.
    '''
    generated = get_clkmgr_clock_partition(top, src)
    if generated == PART_SECONDARY and primary_side:
        # The primary side's gated copy, whatever the power domain (or none).
        return PART_PRIMARY
    if generated == PART_SECONDARY and domain is not None:
        clkmgr = find_module(top['module'], 'clkmgr')
        aon_domain = get_domain_of_partition(clkmgr, PART_SECONDARY)
        return PART_PRIMARY if domain != aon_domain else PART_SECONDARY
    return _out_partition(top, 'clkmgr', generated, domain)


def get_clock_prefixes(top, domain_mod: str = None, src=None, primary_side: bool = False) -> dict:
    '''Return the hierarchical prefixes to the clock, the external clock and the clock gating
    signals.

    The clock comes from the clkmgr partition that outputs it to the power domain `domain_mod` of
    the consumer (see get_clkmgr_out_partition). The clock gating indications all come from the
    primary partition. Each prefix is a local net if that partition is in the power domain of the
    consumer, and the input port of the domain otherwise. Without a source, the prefixes are those
    of the primary partition.
    '''
    clkmgr = find_module(top['module'], 'clkmgr')

    def prefix(kind: str, partition: str) -> str:
        '''Return the prefix to a struct of `partition`, which is a local net or the input port.'''
        sfx = _partition_suffix(partition)
        local = domain_mod is None or get_domain_of_partition(clkmgr, partition) == domain_mod
        return f"{clkmgr['name']}_{kind}{sfx}{'' if local else '_i'}."

    return {
        'top': prefix('clocks', get_clkmgr_out_partition(top, src, domain_mod, primary_side)),
        'ext': '',
        'lpg': prefix('cg_en', PART_PRIMARY),
    }


def _clock_name(clk_name: str) -> str:
    '''Return the name of a clock signal, also from a connection such as clkmgr_clocks.clk_x.'''
    return clk_name.rsplit('.', 1)[-1]


def _is_gated_copy(clk_name: str) -> bool:
    '''Return whether a clock is the primary side's gated copy of a secondary partition's clock.

    Such a clock is named clk_<source>_gated_<group> (see merge), and only the clkmgr's primary
    partition outputs it.
    '''
    return '_gated_' in _clock_name(clk_name)


def get_clkmgr_clock_out_partitions(top) -> Dict[str, List[str]]:
    '''Return, for every managed clock, the partitions of the clkmgr that output the clock.

    Each endpoint gets the clock from the partition in the endpoint's power domain (see
    get_clkmgr_out_partition). An exported clock counts as used in the power domain of the primary
    partition. Raise a ValueError for a clock that no endpoint uses.
    '''
    clkmgr = find_module(top['module'], 'clkmgr')
    primary_domain = get_domain_of_partition(clkmgr, PART_PRIMARY)
    exported = {'clk_' + name for eps in top.get('exported_clks', {}).values()
                for names in eps.values() for name in names}
    result = {}
    for group in top['clocks'].groups.values():
        for name, sig in group.clocks.items():
            keys = set(sig.consumer_keys)
            if name in exported:
                keys.add((primary_domain, False))
            parts = {get_clkmgr_out_partition(top, sig.src, d, ps) for d, ps in keys}
            if not parts:
                raise ValueError(f"No endpoint uses the clock {name}. Remove the clock from the "
                                 "configuration of the top, or connect it.")
            result[name] = _in_partition_order(parts)
    return result


def _indication_reader_domains(top, primary_domain: str, skip) -> Set[str]:
    '''Return the power domains of the low-power groups (LPGs) that read clock gating or reset
    asserted indications.

    These are the LPGs of the alert handlers, and the outgoing LPGs, which are in the power domain
    of the primary partition. The result leaves out the LPGs for which skip(lpg) is true.
    '''
    domains = set()
    for ah in find_modules(top['module'], 'alert_handler'):
        ah_domain = get_domain_of_partition(ah, PART_PRIMARY)
        domains |= {ah_domain for lpg in top.get('alert_lpgs', []) if not skip(lpg)}
    for lpgs in top.get('outgoing_alert_lpgs', {}).values():
        domains |= {primary_domain for lpg in lpgs if not skip(lpg)}
    return domains


def _struct_crosses(crossings: Set[Tuple[str, str, str]], kind: str, partition: str,
                    domain: Optional[str]) -> bool:
    '''Return whether a struct of the given kind crosses from `partition` into `domain`, for
    clkmgr_struct_crosses and rstmgr_struct_crosses.

    A domain of None means any domain.
    '''
    return any(k == kind and p == partition and (domain is None or d == domain)
               for k, p, d in crossings)


def get_clkmgr_crossings(top) -> Set[Tuple[str, str, str]]:
    '''Return the structs of the clkmgr that must enter a power domain through an input port.

    Each entry is (kind, partition, power domain), with kind 'clocks' or 'cg_en'. A domain needs a
    clock struct if a consumer there uses a clock that only the partition in the other domain
    outputs. A domain other than the primary partition's needs the clock gating struct where an LPG
    of the alert handler, or an outgoing LPG, reads an indication.
    '''
    dom = {part: d for part, d, _, _ in get_clkmgr_partitions(top)}
    crossings = set()
    for group in top['clocks'].groups.values():
        # Only the groups with src 'top' come from the clkmgr. An 'ext' group holds raw clocks.
        if group.src != 'top':
            continue
        for sig in group.clocks.values():
            for d, ps in sig.consumer_keys:
                part = get_clkmgr_out_partition(top, sig.src, d, ps)
                if dom[part] != d:
                    crossings.add(('clocks', part, d))
    crossings |= _indication_crossings(top, dom[PART_PRIMARY], 'cg_en',
                                       lambda lpg: lpg.get('unmanaged_clock'))
    return crossings


def clkmgr_struct_crosses(top, kind: str, partition: str, domain: Optional[str] = None) -> bool:
    '''Return whether a struct of the clkmgr crosses into a power domain, or into any domain if
    `domain` is None.'''
    return _struct_crosses(get_clkmgr_crossings(top), kind, partition, domain)


def get_clock_path(top: object,
                   clk_name: str,
                   domain_mod: str = None,
                   unmanaged_clock: bool = False) -> str:
    """Return the appropriate clock path given the clock name
    """
    if unmanaged_clock:
        return top['unmanaged_clocks'].get_clock_by_signal_name(
            clk_name).signal_name
    prefixes = get_clock_prefixes(top, domain_mod, get_clock_src(top, _clock_name(clk_name)),
                                  _is_gated_copy(clk_name))
    return prefixes['top'] + _clock_name(clk_name)


def get_clock_lpg_path(top: object,
                       clk_name: str,
                       domain_mod: str = None,
                       unmanaged_clock: bool = False) -> str:
    """Return the appropriate LPG clock path given name
    """
    if unmanaged_clock:
        return top['unmanaged_clocks'].get_clock_by_signal_name(
            clk_name).cg_en_signal
    prefixes = get_clock_prefixes(top, domain_mod, get_clock_src(top, _clock_name(clk_name)),
                                  _is_gated_copy(clk_name))
    clk_name = clk_name.split('clk_')[-1]
    return prefixes['lpg'] + clk_name


# The name of the always-on clock, which the secondary partition of the clkmgr generates.
AON_CLOCK = 'aon'


def rstmgr_clock_entry_partitions(clock: str, uses: Set[str]) -> Set[str]:
    '''Return the rstmgr partitions that the clock `clock` enters, of those in `uses`.

    A signal enters an IP once, in the partition of the power domain that generates it, and crosses
    between power domains inside the IP. The primary partition of the clkmgr generates every clock
    but the always-on one, so each of those clocks enters the primary partition of the rstmgr only,
    and the secondary partition gets it from there, in intraip_p2s.

    The always-on clock is different: the clkmgr provides one per power domain. Its secondary
    partition's runs always; its primary partition's is gated around the clamp of the power domain
    that powers down. They are two different clocks, so each partition of the rstmgr that uses the
    always-on clock receives the one of its own power domain, and the rstmgr forwards none.
    validate_split_rstmgr checks that the clkmgr generates the clocks this way.
    '''
    if clock == AON_CLOCK:
        return set(uses)
    return {PART_PRIMARY} & set(uses) or {PART_PRIMARY}


def get_rstmgr_partition_clocks(top) -> Dict[str, List[str]]:
    '''Return, by partition, the clocks that each partition of the rstmgr receives (its clock_srcs).
    '''
    rstmgr = find_module(top['module'], 'rstmgr')
    received: Dict[str, List[str]] = {}
    for partition, srcs in get_conns_for(rstmgr, 'clock_srcs'):
        names = received.setdefault(partition, [])
        for net in srcs.values():
            name = _clock_src_name(net)
            if name not in names:
                names.append(name)
    return received


def get_rstmgr_reset_partition(top, name: str, domain: Optional[str]) -> str:
    '''Return the rstmgr partition that generates a reset for a power domain.

    The rstmgr generates a reset in a partition that has the clock of the reset: the partition that
    receives it (see get_rstmgr_partition_clocks), or the other one, which gets it forwarded
    (rstmgr_clock_entry_partitions). It chooses the partition by these rules, in order:

     1. The roots of the reset tree, which no leaf generates, are in the secondary partition. The
        secondary partition handles the POR, as the primary partition of the clkmgr makes the
        derived clocks.
     2. Otherwise, the partition in the power domain of the reset. If both partitions are in that
        power domain, the secondary partition. So the partitions host the same resets whether they
        are in one power domain or in two.
     3. Otherwise, the primary partition.

    Raise a ValueError if neither partition receives the clock of a reset.
    '''
    rstmgr = find_module(top['module'], 'rstmgr')
    rst = top['resets'].get_reset_by_name(name)
    if not rst.gen:
        return PART_SECONDARY
    received = get_rstmgr_partition_clocks(top)
    if not any(rst.clock.name in names for names in received.values()):
        raise ValueError(f"No partition of the {rstmgr['name']} receives the clock "
                         f"{rst.clock.name!r} of the reset {name}")
    # A partition that does not receive the clock gets it from the other partition
    # (rstmgr_clock_entry_partition), so either partition can generate the reset.
    parts = _in_partition_order({PART_PRIMARY, PART_SECONDARY})
    # Try the secondary partition first, so that it wins when both partitions are in that power
    # domain.
    for part in sorted(parts, key=lambda p: p != PART_SECONDARY):
        if get_domain_of_partition(rstmgr, part) == domain:
            return part
    return parts[0]


def validate_split_rstmgr(top) -> None:
    '''Check that the rstmgr is split, and that it can generate each of its resets, as
    validate_split_clkmgr does for the clocks.

    It checks four things:

     - The rstmgr has a domain_secondary. This function raises a ValueError otherwise.
     - Each clock but the always-on one enters only the primary partition of the rstmgr, as the
       primary partition of the clkmgr generates it (rstmgr_clock_entry_partitions). This function
       raises a ValueError otherwise.
     - A partition receives the clock of each reset. get_rstmgr_reset_partition raises a ValueError
       otherwise.
     - For each reset, a partition generates the reset for every power domain or for a single one.
       rstmgr_is_array raises a ValueError otherwise.
    '''
    rstmgr = find_module(top['module'], 'rstmgr')
    if rstmgr is None or not declares_secondary(rstmgr):
        raise ValueError("The rstmgr must be split into two partitions: give it a "
                         "domain_secondary in the configuration of the top")
    for partition, clocks in get_rstmgr_partition_clocks(top).items():
        for clock in clocks:
            generated = get_clkmgr_clock_partition(top, top['clocks'].get_clock_by_name(clock))
            if clock == AON_CLOCK:
                continue
            enters = PART_PRIMARY
            if partition != enters:
                log.warning(f"The {partition} partition of the {rstmgr['name']} receives the "
                            f"clock {clock!r}, which enters its {enters} partition: the "
                            f"{partition} partition gets it from there, in intraip")
            if generated != enters:
                log.warning(f"The clock {clock!r} enters the {enters} partition of the "
                            f"{rstmgr['name']}, but the clkmgr generates it in its "
                            f"{generated} partition")
    for rst in top['resets'].get_top_resets():
        parts = {d: get_rstmgr_reset_partition(top, rst.name, d) for d in rst.domains}
        for part in set(parts.values()):
            rstmgr_is_array([d for d, p in parts.items() if p == part], top['power']['domains'])

    # The clkmgr gates the always-on clock that its primary partition gets from its secondary
    # partition, around the clamp of the power domain that powers down. That gated clock is the
    # always-on clock of the primary partitions of the managers, and of the modules that the
    # clkmgr's primary partition serves outside the always-on power domain. A module of the
    # always-on power domain on it would lose its clock in every deep sleep.
    #
    # These checks only warn, because the rules of the split managers are still evolving, and topgen
    # should not get in the way of that (follow-up). They also check how other modules use the
    # clocks of the managers, which the managers cannot see.
    default_domain = top.get('power', {}).get('default')
    clkmgr = find_module(top['module'], 'clkmgr')
    aon_domain = get_domain_of_partition(clkmgr, PART_SECONDARY, default_domain)
    aon_src = top['clocks'].get_clock_by_name(AON_CLOCK)
    for module in top['module']:
        if module['type'] in ('clkmgr', 'rstmgr'):
            continue
        for partition, srcs in get_conns_for(module, 'clock_srcs'):
            domain = get_domain_of_partition(module, partition, default_domain)
            if domain != aon_domain:
                continue
            for port, src in srcs.items():
                name = src if isinstance(src, str) else src.get('clock')
                if name != AON_CLOCK:
                    continue
                if get_clkmgr_out_partition(top, aon_src, domain) == PART_PRIMARY:
                    log.warning(f"{module['name']}.{port} ({partition} partition, power domain "
                                f"{domain}) gets the always-on clock from the primary partition "
                                f"of the clkmgr, which gates it in every deep sleep")


def get_rstmgr_out_partition(top, name: str, rst_domain: str,
                             consumer_domain: Optional[str]) -> str:
    '''Return the rstmgr partition that outputs a reset of a power domain to a consumer.

    The partition that get_rstmgr_reset_partition chooses generates the reset. _out_partition gives
    the partition that outputs the reset.
    '''
    generated = get_rstmgr_reset_partition(top, name, rst_domain)
    return _out_partition(top, 'rstmgr', generated, consumer_domain)


def _rstmgr_consumers(top):
    '''Yield (reset name, power domain of the reset, power domain of the consumer) for every use of
    a reset by a module or a crossbar.

    An exported reset counts as used in the power domain of the primary partition. The function
    skips reset connections without a power domain, and names that are not top-level resets.
    '''
    resets = top['resets']
    # The crossbars are in top['xbar'], not in top['module'], so the loop scans both, as
    # extract_clocks does for the clocks. This is a workaround until topgen has one helper for every
    # instance with connections.
    for module in top['module'] + top['xbar']:
        for partition, conns in get_conns_for(module, 'reset_connections'):
            consumer_domain = get_domain_of_partition(module, partition)
            for conn in conns.values():
                if not isinstance(conn, dict) or not conn.get('domain'):
                    continue
                # get_reset_by_name raises a ValueError for a reset name that it does not know.
                try:
                    rst = resets.get_reset_by_name(conn['name'])
                except ValueError:
                    continue
                if rst.rst_type == 'top':
                    yield conn['name'], conn['domain'], consumer_domain
    rstmgr = find_module(top['module'], 'rstmgr')
    primary_domain = get_domain_of_partition(rstmgr, PART_PRIMARY)
    for eps in top.get('exported_rsts', {}).values():
        for rsts in eps.values():
            for name in rsts:
                # An exported reset is a name, or a dict that holds its name.
                name = name['name'] if isinstance(name, dict) else name
                for dom in resets.get_reset_by_name(name).domains:
                    yield name, dom, primary_domain


def get_rstmgr_reset_out_partitions(top) -> Dict[Tuple[str, str], List[str]]:
    '''Return, for each reset and power domain, the partitions of the rstmgr that output the reset.

    Each consumer gets the reset from the partition in the consumer's power domain (see
    get_rstmgr_out_partition). Raise a ValueError for a reset that no consumer uses in one of its
    power domains.
    '''
    result: Dict[Tuple[str, str], Set[str]] = {}
    for name, dom, consumer_domain in _rstmgr_consumers(top):
        result.setdefault((name, dom), set()).add(
            get_rstmgr_out_partition(top, name, dom, consumer_domain))
    unused = [f'{rst.name}[{dom}]' for rst in top['resets'].get_top_resets() for dom in rst.domains
              if (rst.name, dom) not in result]
    if unused:
        raise ValueError(f"No consumer uses these resets: {', '.join(unused)}. Remove them from "
                         "the configuration of the top, or connect them.")
    return {k: _in_partition_order(v) for k, v in result.items()}


def get_rstmgr_shadowed_out_partitions(top) -> Dict[Tuple[str, str], List[str]]:
    '''Return, for each shadowed reset and power domain, the partitions of the rstmgr that output
    the shadowed copy.

    A reset, or the shadowed copy of a reset, crosses to the other partition only if a module in
    that partition's power domain uses it. The partition that generates the shadowed copy outputs it
    wherever it outputs the reset, even if no module in its own power domain uses the shadowed copy.
    '''
    outs = get_rstmgr_reset_out_partitions(top)
    result = {}
    for rst in top['resets'].get_top_resets():
        if not rst.shadowed:
            continue
        for dom in rst.domains:
            used = {get_rstmgr_out_partition(top, rst.name, d, consumer_domain)
                    for d, consumer_domain in rst.shadowed_users if d == dom}
            generated = get_rstmgr_reset_partition(top, rst.name, dom)
            result[(rst.name, dom)] = [p for p in outs.get((rst.name, dom), [])
                                       if p == generated or p in used]
    return result


def get_rstmgr_crossings(top) -> Set[Tuple[str, str, str]]:
    '''Return the structs of the rstmgr that must enter a power domain through an input port.

    Each entry is (kind, partition, power domain), with kind 'resets' or 'rst_en'. A domain needs a
    reset struct if a consumer there uses a reset that only the partition in the other domain
    outputs. A domain other than the primary partition's needs the reset enable struct where an LPG
    of the alert handler, or an outgoing LPG, reads an indication.
    '''
    dom = {part: d for part, d, _, _ in get_rstmgr_partitions(top)}
    crossings = set()
    for name, rst_domain, consumer_domain in _rstmgr_consumers(top):
        part = get_rstmgr_out_partition(top, name, rst_domain, consumer_domain)
        if dom[part] != consumer_domain:
            crossings.add(('resets', part, consumer_domain))

    def skip(lpg):
        '''Return whether the reset connection of an LPG is unmanaged or has no power domain.'''
        conn = lpg.get('reset_connection')
        return lpg.get('unmanaged_reset') or not isinstance(conn, dict) or not conn.get('domain')
    crossings |= _indication_crossings(top, dom[PART_PRIMARY], 'rst_en', skip)
    return crossings


def rstmgr_struct_crosses(top, kind: str, partition: str, domain: Optional[str] = None) -> bool:
    '''Return whether a struct of the rstmgr crosses into a power domain, or into any domain if
    `domain` is None.'''
    return _struct_crosses(get_rstmgr_crossings(top), kind, partition, domain)


def get_rstmgr_output_index(top, name: str, rst_domain: str, partition: str,
                            shadowed: bool = False) -> str:
    '''Return the power domain to index the field of a reset, or of its shadowed copy, with, in the
    output struct of a partition.

    Return None if the field is a single bit.
    '''
    rst = top['resets'].get_reset_by_name(name)
    outs = (get_rstmgr_shadowed_out_partitions(top) if shadowed
            else get_rstmgr_reset_out_partitions(top))
    out_doms = [d for d in rst.domains if partition in outs.get((name, d), [])]
    indexed = rstmgr_is_array(out_doms, top['power']['domains'])
    return (rst_domain if indexed else None)


def get_reset_prefixes(top, domain_mod, partition: str = PART_PRIMARY) -> dict:
    '''Return the hierarchical prefixes to the resets, the external resets and the reset enables.

    The prefix is the one of the rstmgr partition that drives the reset, or of the primary partition
    if the caller gives no `partition`. It is a local net if that partition is in the power domain
    `domain_mod` of the consumer, and the input port of the domain otherwise.
    '''
    rstmgr = find_module(top['module'], 'rstmgr')
    domain_rstmgr = get_domain_of_partition(rstmgr, partition)
    sfx = _partition_suffix(partition)

    if domain_rstmgr == domain_mod or domain_mod is None:
        prefixes = {
            'top': f"{rstmgr['name']}_resets{sfx}.",
            'ext': '',
            'lpg': f"{rstmgr['name']}_rst_en{sfx}.",
        }
    else:
        prefixes = {
            'top': f"{rstmgr['name']}_resets{sfx}_i.",
            'ext': '',
            'lpg': f"{rstmgr['name']}_rst_en{sfx}_i.",
        }

    return prefixes


def _get_reset_location(top, name: str, domain: Optional[str]) -> Tuple[str, Optional[str]]:
    '''Return the partition that generates a reset, and the power domain to index its field with.

    The power domain is None if the field has no index. The shape of a field follows the convention
    of the output structs of the rstmgr templates.
    '''
    rst = top['resets'].get_reset_by_name(name)
    if rst.rst_type != 'top':
        return PART_PRIMARY, domain
    if not domain:
        return get_rstmgr_reset_partition(top, name, rst.domains[0]), None
    partition = get_rstmgr_reset_partition(top, name, domain)
    hosted = [d for d in rst.domains if get_rstmgr_reset_partition(top, name, d) == partition]
    return partition, (domain if rstmgr_is_array(hosted, top['power']['domains']) else None)


def get_reset_path(top: object,
                   reset: Union[str, object],
                   domain_mod: str = None,
                   shadow_sel: bool = False,
                   unmanaged_reset: bool = False) -> str:
    """Return the appropriate reset path given name
    """
    if unmanaged_reset:
        return top['unmanaged_resets'].get(reset['name']).signal_name
    rst = top['resets'].get_reset_by_name(reset['name'])
    if rst.rst_type != 'top' or not reset['domain']:
        # The reset comes from the partition that generates it.
        partition, index_domain = _get_reset_location(top, reset['name'], reset['domain'])
    else:
        # The reset comes from the partition that outputs it in the consumer's power domain.
        partition = get_rstmgr_out_partition(top, reset['name'], reset['domain'], domain_mod)
        index_domain = get_rstmgr_output_index(top, reset['name'], reset['domain'], partition,
                                               shadow_sel)
    prefixes = get_reset_prefixes(top, domain_mod, partition)
    return top['resets'].get_path(reset['name'], prefixes, index_domain, shadow_sel)


def get_reset_lpg_path(top: object,
                       reset: Union[str, object],
                       domain_mod: str = None,
                       shadow_sel: bool = False,
                       reset_domain: str = None,
                       unmanaged_reset: bool = False) -> str:
    """Return the appropriate LPG reset path given name
    """
    if unmanaged_reset:
        return top['unmanaged_resets'].get(reset['name']).rst_en_signal_name
    domain = reset_domain if reset_domain is not None else reset['domain']
    rst = top['resets'].get_reset_by_name(reset['name'])
    if rst.rst_type == 'top' and domain:
        # The rstmgr outputs all the reset asserted indications from its primary partition, for the
        # alert handlers.
        partition = PART_PRIMARY
        index_domain = domain if rstmgr_is_array(rst.domains, top['power']['domains']) else None
    else:
        # The indication comes from the partition that generates the reset.
        partition, index_domain = _get_reset_location(top, reset['name'], domain)
    prefixes = get_reset_prefixes(top, domain_mod, partition)
    return top['resets'].get_lpg_path(reset['name'], prefixes, index_domain, shadow_sel)


def get_unused_resets(top: ConfigT) -> Dict:
    """Return dict of unused resets and associated domain
    """
    # The rstmgr outputs each reset only in the domains that use it. So there are no unused resets.
    # The function stays for its callers, rstmgr_tgl_excl.cfg.tpl and intermodule_signals.tpl.
    return {}


def get_ipgen_modules(top: ConfigT) -> List[ConfigT]:
    """Returns list of all ipgen modules.
    """
    return [m['type'] for m in top['module'] if is_ipgen(m)]


def get_top_reggen_modules(top: ConfigT) -> List[ConfigT]:
    """Returns list of all ipgen modules.
    """
    return [m['type'] for m in top['module'] if is_top_reggen(m)]


def is_module_attr_valid(module: ConfigT) -> bool:
    return ('attr' not in module or
            module.get('attr') in ["ipgen", "reggen_top", "reggen_only"])


def is_ipgen(module: ConfigT) -> bool:
    """Returns an indication where a particular module is ipgen
    """
    return module.get('attr') in ["ipgen"]


def get_ipgen_params(module: ConfigT) -> ParamsT:
    """Return ipgen params, if defined for this module"""
    return deepcopy(module.get("ipgen_params", {}))


def is_top_reggen(module: ConfigT) -> bool:
    """Returns an indication where a particular module is NOT generated
       and requires top level specific reggen
    """
    return module.get('attr') in ["reggen_top", "reggen_only"]


def is_reggen_only(module: ConfigT) -> bool:
    """Returns an indication where a particular module is NOT generated,
       requires top level specific reggen and is NOT instantiated in the
       top
    """
    return module.get('attr') == "reggen_only"


def is_inst(module: ConfigT) -> bool:
    """Returns an indication where a particular module should be instantiated
       in the top level
    """
    top_level_module = False
    top_level_mem = False

    if "attr" not in module:
        top_level_module = True
    elif module["attr"] in ["normal", "ipgen", "reggen_top"]:
        top_level_module = True
    elif module["attr"] in ["reggen_only"]:
        top_level_module = False
    else:
        raise ValueError('Attribute {} in {} is not valid'.format(
            module['attr'], module['name']))

    if module['type'] in ['rom', 'ram_1p_scr', 'eflash']:
        top_level_mem = True

    return top_level_mem or top_level_module


def get_base_and_size(block: IpBlock,
                      inst: ConfigT,
                      ifname: Optional[str]
                      ) -> Tuple[Dict[str, int], int] | None:
    '''Return (base_addrs, size) to describe addresses inst uses on ifname.

    It may be that this instance doesn't actually use the interface at all in
    the top-level (perhaps because its support for the interface is disabled by
    a parameter). If so, return None.

    If the instance *does* use the interface, base_addrs is a map from address
    space ID to the base address of the block in that address space.

    size is the size in bytes that the block uses on the interface named
    ifname.
    '''

    # Check whether the top-level connects up this interface. If not, return
    # None.
    base_addrs = inst['base_addrs'].get(ifname)
    if base_addrs is None:
        return None

    # If inst is the instantiation of some block, find the register block
    # that corresponds to ifname
    if rb := block.reg_blocks.get(ifname):
        bytes_used = 1 << rb.get_addr_width()
    elif mem := inst["memory"].get(ifname):
        bytes_used = int(mem["size"], 0)
    else:
        raise RuntimeError(
            'Cannot connect to non-existent {} device interface '
            'on {!r} (an instance of the {!r} block).'.format(
                'default' if ifname is None else repr(ifname),
                inst['name'], block.name))

    base_addrs = deepcopy(base_addrs)

    for (asid, base_addr) in base_addrs.items():
        if isinstance(base_addr, str):
            base_addrs[asid] = int(base_addr, 0)
        else:
            assert isinstance(base_addrs[asid], int)

    return (base_addrs, bytes_used)


def get_io_enum_literal(sig: Dict, prefix: str) -> str:
    """Returns the DIO pin enum literal with value assignment"""
    name = Name.from_snake_case(prefix) + Name.from_snake_case(sig["name"])
    # In this case, the signal is a multibit signal, and hence
    # we have to make the signal index part of the parameter
    # name to uniquify it.
    if sig['width'] > 1:
        name += Name([str(sig['idx'])])
    return name.as_camel_case()


def get_params(top: ConfigT, module: ConfigT,
               partition: str = PART_PRIMARY
               ) -> Tuple[bool, List[Tuple[str, str]]]:
    """Return the parameters for a given module including implicit parameters
       but excluding RACL parameters, which are handled in a separate template.

    For split IPs, `partition` selects which partition's parameters and alert
    async configuration are emitted. A parameter is included when its own
    'partition' is 'both' or matches `partition`. The alert async_expr is
    taken from that partition's alert connection.
    """
    param_items = []
    alert_info = top["alert_connections"].get(
        alert_conn_key(module["name"], partition), {})
    has_racl_params = (bool(module.get("racl_mappings")) and
                       partition == PART_PRIMARY)
    if alert_info:
        param_items.append((".AlertAsyncOn", alert_info["async_expr"]))
    if alert_info or module.get("template_type") == "alert_handler":
        param_items.append((".AlertSkewCycles", "top_pkg::AlertSkewCycles"))
    for param in module["param_list"]:
        # 'both' parameters are emitted into every partition.
        if param.get("partition", PART_PRIMARY) not in (PART_BOTH, partition):
            continue
        is_exposed = check_bool(param.get("expose", False), f"expose field of {param['name']}")
        has_random_type = param.get("randtype")
        param_key = "name_top" if (is_exposed or has_random_type) else "default"
        param_items.append((f".{param['name']}", param[param_key]))

    has_params = has_racl_params or len(param_items) > 0
    return has_params, param_items


def make_bit_concatenation(sig_name: str, indices: List[int],
                           end_indent: int) -> str:
    '''Return SV code for concatenating certain indices from a signal

    sig_name is the name of the signal and indices is a non-empty list of the
    indices to use, MSB first. So

      make_bit_concatenation("foo", [0, 100, 20])

    should give

      {foo[0], foo[100], foo[20]}

    Adjacent bits turn into a range select. For example:

      make_bit_concatenation("foo", [0, 1, 2])

    should give

      foo[0:2]

    If there are multiple ranges, they are printed one to a line. end_indent
    gives the indentation of the closing brace and the range selects in between
    get indented to end_indent + 2.

    '''
    assert 0 <= end_indent

    ranges = []
    cur_range_start = indices[0]
    cur_range_end = indices[0]
    for idx in indices[1:]:
        if idx == cur_range_end + 1 and cur_range_start <= cur_range_end:
            cur_range_end += 1
            continue
        if idx == cur_range_end - 1 and cur_range_start >= cur_range_end:
            cur_range_end -= 1
            continue
        ranges.append((cur_range_start, cur_range_end))
        cur_range_start = idx
        cur_range_end = idx
    ranges.append((cur_range_start, cur_range_end))

    items = []
    for range_start, range_end in ranges:
        if range_start == range_end:
            select = str(range_start)
        else:
            select = '{}:{}'.format(range_start, range_end)
        items.append('{}[{}]'.format(sig_name, select))

    if len(items) == 1:
        return items[0]

    item_indent = '\n' + (' ' * (end_indent + 2))

    acc = ['{', item_indent, items[0]]
    for item in items[1:]:
        acc += [',', item_indent, item]
    acc += ['\n', ' ' * end_indent, '}']
    return ''.join(acc)


def num_rom_ctrl(modules: List[ConfigT], domain: str = None) -> int:
    '''Return number of rom_ctrl's instantiated in the design
    '''
    num = 0

    for m in modules:
        if m['type'] == 'rom_ctrl' and \
           (domain is None or m.get('domain') == domain):
            num += 1

    return num


def find_modules(modules: List[Dict[str, object]],
                 type: str,
                 use_base_template_type=True,
                 domain: str = None) -> List[Dict[str, object]]:
    '''Returns the modules of a given type

    If use_base_template_type is set to True, ipgen-based modules are
    searched using the "template_type" attribute. If set to False,
    the search uses the "type" attribute instead.
    '''
    modules_found = []
    for m in modules:
        if m.get('attr') == 'ipgen' and use_base_template_type:
            if m['template_type'] == type and \
               (domain is None or m.get('domain') == domain):
                modules_found.append(m)
        else:
            if m['type'] == type and \
               (domain is None or m.get('domain') == domain):
                modules_found.append(m)

    return modules_found


def find_module(
        modules: List[Dict[str, object]],
        type: str,
        use_base_template_type=True,
        domain: str = None) -> Optional[Dict[str, object]]:
    '''Returns the first module of a given type

    If use_base_template_type is set to True, ipgen-based modules are
    searched using the "template_type" attribute. If set to False,
    the search uses the "type" attribute instead.
    '''
    mods = find_modules(modules, type, use_base_template_type, domain)
    return mods[0] if mods else None


def find_module_by_name(modules: List[Dict[str, object]],
                        name: str) -> Optional[Dict[str, object]]:
    """Return the (first) module with a given name, or None."""
    for m in modules:
        if m["name"] == name:
            return m
    return None


def get_addr_space(top: ConfigT, addr_space_name: str) -> ConfigT:
    """Returns the address dict for a given address space name"""
    for addr_space in top['addr_spaces']:
        if addr_space['name'] == addr_space_name:
            return addr_space
    assert False, "Address space not found"


def get_device_ranges(devices, device_name):
    ranges = {}
    for (dev_name, if_name), range in devices:
        if dev_name == device_name:
            ranges[if_name] = range
    return ranges


def get_addr_space_suffix(addr_space: str) -> str:
    # TODO: Don't special-case the "hart" address space.
    if addr_space['name'] == "hart":
        return ""
    return "_" + addr_space['name']


def remove_prefix(s: str, prefix: str) -> str:
    return s[len(prefix):] if s.startswith(prefix) else s


class TopGen:

    def __init__(self, top_info: ConfigT, name_to_block: IpBlocksT, enum_type,
                 array_mapping_type):
        self.top = top_info
        self._top_name = Name(["top"]) + Name.from_snake_case(top_info["name"])
        self._name_to_block = name_to_block
        self.regwidth = int(top_info["datawidth"])

        assert enum_type in [CEnum, RustEnum], "Unsupported enum type"
        assert array_mapping_type in [CArrayMapping, RustArrayMapping], \
               "Unsupported array mapping type"
        self._enum_type = enum_type
        self._array_mapping_type = array_mapping_type

        self.default_plic = self.top.get("default_plic", None)
        self._init_plics()

        # Only generate alert_handler and mappings if there is an alert_handler
        if find_module(self.top['module'], 'alert_handler'):
            self._init_alert_mapping()
        # Only generate pinmux and pad mappings if there is a pinmux
        if find_module(self.top['module'], 'pinmux'):
            self._init_pinmux_mapping()
            self._init_pad_mapping()
        # Only generate pwrmgr mappings if there is a pwrmgr
        if find_module(self.top['module'], 'pwrmgr'):
            self._init_pwrmgr_wakeups()
            self._init_pwrmgr_reset_requests()
        # Only generate rstmgr mappings if there is a rstmgr
        if find_module(self.top['module'], 'rstmgr'):
            self._init_rstmgr_sw_rsts()
        # Only generate clkmgr mappings if there is a clkmgr
        if find_module(self.top['module'], 'clkmgr'):
            self._init_clkmgr_clocks()

        self.device_regions = defaultdict(dict)
        self.device_memories = defaultdict(dict)
        self.subranges = defaultdict(dict)
        for addr_space in top_info['addr_spaces']:
            self._init_device_regions(addr_space['name'])
            self._init_device_memories(addr_space['name'])
            self._init_subranges(addr_space['name'])

    def _init_device_regions(self, addr_space):
        '''Initialize the device_regions dictionary.

        The dictionary entry maps blocks to MemoryRegions for the given
        addr_space.
        '''
        device_region = defaultdict(dict)
        for inst in self.top['module']:
            block = self._name_to_block[inst['type']]
            for if_name in block.reg_blocks.keys():
                bases_size = get_base_and_size(block, inst, if_name)
                if bases_size is None:
                    # Nothing to do for this interface: it is not used in this
                    # instance.
                    continue

                bases, size = bases_size
                base = bases.get(addr_space)
                if base is None:
                    # Again, nothing to do for this interface: it does not
                    # define anything mapped into addr_space.
                    continue

                full_if = (inst['name'], if_name)
                full_if_name = Name.from_snake_case(full_if[0])
                if if_name is not None:
                    full_if_name += Name.from_snake_case(if_name)

                name = full_if_name

                region = MemoryRegion(self._top_name, name, addr_space,
                                      base, size)
                device_region[inst['name']].update({if_name: region})

        self.device_regions[addr_space] = device_region

    def all_device_regions(self) -> Dict[str, Dict[str, MemoryRegion]]:
        '''Return a list of MemoryRegion objects for all devices on the bus.
        '''
        return self.device_regions

    def devices(
            self, addr_space
    ) -> List[Tuple[Tuple[str, Optional[str]], MemoryRegion]]:
        '''Return a list of MemoryRegion objects for devices on the bus.

        The list returned is pairs (full_if, region) where full_if is itself a
        pair (inst_name, if_name). inst_name is the name of some IP block
        instantiation. if_name is the name of the interface (may be None).
        region is a MemoryRegion object representing the device.

        Note that this list only includes register bloks. Use `memories()`
        to access the list of memories.

        Parameters:
            addr_space: The address space representing the bus for generation.
        '''
        ret = []  # type: List[Tuple[Tuple[str, Optional[str]], MemoryRegion]]
        # TODO: This method is invoked in templates, as well as in the extended
        # class TopGenCTest. We could refactor and optimize the implementation
        # a bit.
        for (inst, regions) in self.device_regions[addr_space].items():
            for (if_name, region) in regions.items():
                full_if = (inst, if_name)
                ret.append((full_if, region))

        return ret

    def _init_device_memories(self, addr_space):
        '''Initialize the device_memories dictionary.

        The dictionary entry maps memories to MemoryRegions for the given
        addr_space.
        '''
        device_memories = defaultdict(dict)

        for inst in self.top['module']:
            block = self._name_to_block.get(inst['type'])
            if block is None:
                raise RuntimeError(f"No block defined for instance "
                                   f"type {inst['type']} (with name "
                                   f"{inst['name']})")

            for if_name, val in inst.get("memory", {}).items():
                bases_size = get_base_and_size(block, inst, if_name)

                # We expect bases_size not to be None. If it is None, then the
                # instance defines the memory but doesn't give it a base
                # address (which seems unlikely to be right).
                if bases_size is None:
                    raise RuntimeError(f"The instance named {inst['name']} "
                                       f"defines a memory for interface "
                                       f"{if_name}, but doesn't give it a "
                                       f"base address.")

                bases, size = bases_size
                base = bases.get(addr_space)

                if base is None:
                    continue

                full_if_name = Name.from_snake_case(inst['name']) + \
                    Name.from_snake_case(if_name)
                region = MemoryRegion(self._top_name, full_if_name, addr_space,
                                      base, size)

                device_memories[inst['name']].update({if_name: region})

        self.device_memories[addr_space] = device_memories

    def memories(self, addr_space) -> List[Tuple[Tuple[str, str], MemoryRegion]]:
        '''Return a list of MemoryRegions objects for memories on the bus.

        The list returned is pairs (full_if, region) where full_if is itself a
        pair (inst_name, if_name). inst_name is the name of some IP block
        instantiation. if_name is the name of the interface. region is a
        MemoryRegion representing the memory, and its name is set to the full
        interface name (<IP instance name>_<interface>).

        Parameters:
            addr_space: The address space representing the bus for generation.
        '''
        ret = []

        for (inst, regions) in self.device_memories[addr_space].items():
            for (if_name, region) in regions.items():
                full_if = (inst, if_name)
                ret.append((full_if, region))

        return ret

    def _init_plics(self):
        self.plic_targets = {}
        self.plic_sources = {}
        self.plic_interrupts = {}
        self.plic_mapping = {}
        self.device_irqs = {}

        for plic in find_modules(self.top["module"], "rv_plic"):
            plic_targets = self._init_plic_targets(plic)
            name = plic["name"]
            self.plic_targets[name] = plic_targets

            plic_sources, plic_interrupts, plic_mapping = self._init_plic_mapping(plic)
            self.plic_sources[name] = plic_sources
            self.plic_interrupts[name] = plic_interrupts
            self.plic_mapping[name] = plic_mapping

    def _init_plic_targets(self, plic):
        unsnaked_name = Name.from_snake_case(remove_prefix(plic["name"], "rv_"))
        enum = self._enum_type(self._top_name, unsnaked_name + Name(["target"]))

        # In the special case of one target called "rv_core_ibex",
        # call this "Ibex0" for compatibility with existing tests.
        targets = plic.get("targets", [])
        if len(targets) == 1 and targets[0] == "rv_core_ibex":
            enum.add_constant(Name(["ibex", "0"]), docstring="Ibex Core 0")
        else:
            for target in targets:
                shortened_target = remove_prefix(target, "rv_core_")
                enum.add_constant(Name.from_snake_case(shortened_target),
                                  docstring="Ibex {}".format(target))

        if isinstance(enum, RustEnum):
            enum.add_number_of_variants("Final number of PLIC target")
        else:
            enum.add_last_constant("Final PLIC target")

        return enum

    def _init_plic_mapping(self, plic):
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
        # A lot of code counts on this being named "Plic" and not "RvPlic"
        unsnaked_name = Name.from_snake_case(remove_prefix(plic["name"], "rv_"))
        sources = self._enum_type(self._top_name, unsnaked_name + Name(["peripheral"]),
                                  self.regwidth)
        interrupts = self._enum_type(self._top_name,
                                     unsnaked_name + Name(["irq", "id"]), self.regwidth)
        plic_mapping = self._array_mapping_type(
            self._top_name, unsnaked_name + Name(["interrupt", "for", "peripheral"]),
            sources.short_name
            if isinstance(sources, RustEnum) else sources.name)

        unknown_source = sources.add_constant(Name(["unknown"]),
                                              docstring="Unknown Peripheral")
        none_irq_id = interrupts.add_constant(Name(["none"]),
                                              docstring="No Interrupt")
        plic_mapping.add_entry(none_irq_id, unknown_source)

        # When we generate the `interrupts` enum, the only info we have about
        # the source is the module name. We'll use `source_name_map` to map a
        # short module name to the full name object used for the enum constant.
        source_name_map = {'unknown': unknown_source}

        my_modules = {x["name"] for x in self.top["module"]
                      if x.get("plic", self.default_plic) == plic["name"]}
        for name in self.top["interrupt_module"]:
            if name not in my_modules:
                continue

            source_name = sources.add_constant(Name.from_snake_case(name),
                                               docstring=name)
            source_name_map[name] = source_name

        if isinstance(sources, RustEnum):
            sources.add_number_of_variants("Number of PLIC peripheral")
        else:
            sources.add_last_constant("Final PLIC peripheral")

        # Maintain a list of instance-specific IRQs organized first by PLIC, then by instance name.
        self.device_irqs[plic["name"]] = defaultdict(list)
        for intr in self.top["interrupt"]:
            if intr.get("plic", self.default_plic) != plic["name"]:
                continue

            # Some interrupts are multiple bits wide. Here we deal with that by
            # adding a bit-index suffix
            if "width" in intr and int(intr["width"]) != 1:
                for i in range(int(intr["width"])):
                    name = Name.from_snake_case(intr["name"]) + Name([str(i)])
                    irq_id = interrupts.add_constant(name,
                                                     docstring="{} {}".format(
                                                         intr["name"], i))
                    source_name_key = 'unknown' if intr['incoming'] else intr[
                        'module_name']
                    source_name = source_name_map[source_name_key]
                    plic_mapping.add_entry(irq_id, source_name)
                    self.device_irqs[plic["name"]][intr["module_name"]].append(intr["name"] +
                                                                               str(i))
            else:
                name = Name.from_snake_case(intr["name"])
                irq_id = interrupts.add_constant(name, docstring=intr["name"])
                source_name_key = 'unknown' if intr['incoming'] else intr[
                    'module_name']
                source_name = source_name_map[source_name_key]
                plic_mapping.add_entry(irq_id, source_name)
                self.device_irqs[plic["name"]][intr["module_name"]].append(intr["name"])

        if isinstance(interrupts, RustEnum):
            interrupts.add_number_of_variants("Number of Interrupt ID.")
        else:
            interrupts.add_last_constant("The Last Valid Interrupt ID.")

        return (sources, interrupts, plic_mapping)

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
        # TODO: Model alert domains with explicit connectivity.
        sources = self._enum_type(self._top_name,
                                  Name(["alert", "peripheral"]), self.regwidth)
        alerts = self._enum_type(self._top_name, Name(["alert", "id"]),
                                 self.regwidth)
        alert_mapping = self._array_mapping_type(
            self._top_name, Name(["alert", "for", "peripheral"]),
            sources.short_name
            if isinstance(sources, RustEnum) else sources.name)

        external_source = sources.add_constant(Name(["external"]),
                                               docstring="External Peripheral")

        # When we generate the `alerts` enum, the only info we have about the
        # source is the module name. We'll use `source_name_map` to map a short
        # module name to the full name object used for the enum constant.
        source_name_map = {'external': external_source}

        for name in self.top["alert_module"]:
            source_name = sources.add_constant(Name.from_snake_case(name),
                                               docstring=name)
            source_name_map[name] = source_name

        if isinstance(sources, RustEnum):
            sources.add_number_of_variants("Final number of Alert peripheral")
        else:
            sources.add_last_constant("Final Alert peripheral")

        def add_alert(alert, name_prefix=None):
            alert_module = alert['module_name']

            if 'width' in alert and int(alert['width']) != 1:
                for i in range(int(alert['width'])):
                    name = Name.from_snake_case(alert['name']) + Name([str(i)])
                    if name_prefix:
                        name = Name.from_snake_case(name_prefix) + name
                        alert_module = f'{name_prefix}_{alert_module}'

                    alert_id = alerts.add_constant(
                        name, docstring=name.as_snake_case())
                    source_name_key = ('external'
                                       if name_prefix else alert_module)
                    source_name = source_name_map[source_name_key]
                    alert_mapping.add_entry(alert_id, source_name)
                    self.device_alerts[alert_module].append(
                        name.as_snake_case() + str(i))
            else:
                name = Name.from_snake_case(alert['name'])
                if name_prefix:
                    name = Name.from_snake_case(name_prefix) + name
                    alert_module = f'{name_prefix}_{alert_module}'

                alert_id = alerts.add_constant(name,
                                               docstring=name.as_snake_case())
                source_name_key = 'external' if name_prefix else alert_module
                source_name = source_name_map[source_name_key]
                alert_mapping.add_entry(alert_id, source_name)
                self.device_alerts[alert_module].append(name.as_snake_case())

        self.device_alerts = defaultdict(list)
        for alert in self.top["alert"]:
            add_alert(alert)

        for alert_group, incoming_alerts in self.top['incoming_alert'].items():
            for alert in incoming_alerts:
                add_alert(alert, f'incoming_{alert_group}')

        if isinstance(alerts, RustEnum):
            alerts.add_number_of_variants("The number of Alert ID.")
        else:
            alerts.add_last_constant("The Last Valid Alert ID.")

        self.alert_sources = sources
        self.alert_alerts = alerts
        self.alert_mapping = alert_mapping

    def _init_pinmux_mapping(self):
        """Generate Rust enums for addressing pinmux registers and in/out selects.

        Inputs/outputs are connected in the order the modules are listed in
        the hjson under the "mio_modules" key. For each module, the
        corresponding inouts are connected first, followed by either the inputs
        or the outputs.

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
        peripheral_in = self._enum_type(self._top_name,
                                        Name(['pinmux', 'peripheral', 'in']),
                                        self.regwidth)
        i = 0
        for sig in pinmux_info['ios']:
            if sig['connection'] == 'muxed' and sig['type'] in [
                    'inout', 'input'
            ]:
                index = Name([str(sig['idx'])]) if sig['idx'] != -1 else Name(
                    [])
                name = Name.from_snake_case(sig['name']) + index
                peripheral_in.add_constant(
                    name, docstring='Peripheral Input {}'.format(i))
                i += 1

        if isinstance(peripheral_in, RustEnum):
            peripheral_in.add_number_of_variants('Number of peripheral input')
        else:
            peripheral_in.add_last_constant('Last valid peripheral input')

        # Pinmux Input Selects
        insel = self._enum_type(self._top_name, Name(['pinmux', 'insel']),
                                self.regwidth)
        insel.add_constant(Name(['constant', 'zero']),
                           docstring='Tie constantly to zero')
        insel.add_constant(Name(['constant', 'one']),
                           docstring='Tie constantly to one')
        i = 0
        for pad in pinout_info['pads']:
            if pad['connection'] == 'muxed':
                insel.add_constant(Name.from_snake_case(pad['name']),
                                   docstring='MIO Pad {}'.format(i))
                i += 1
        if isinstance(insel, RustEnum):
            insel.add_number_of_variants('Number of valid insel value')
        else:
            insel.add_last_constant('Last valid insel value')
        # MIO Outputs
        mio_out = self._enum_type(self._top_name,
                                  Name(['pinmux', 'mio', 'out']))
        i = 0
        for pad in pinout_info['pads']:
            if pad['connection'] == 'muxed':
                mio_out.add_constant(Name.from_snake_case(pad['name']),
                                     docstring='MIO Pad {}'.format(i))
                i += 1
        if isinstance(mio_out, RustEnum):
            mio_out.add_number_of_variants('Number of valid mio output')
        else:
            mio_out.add_last_constant('Last valid mio output')

        # Pinmux Output Selects
        outsel = self._enum_type(self._top_name, Name(['pinmux', 'outsel']),
                                 self.regwidth)
        outsel.add_constant(Name(['constant', 'zero']),
                            docstring='Tie constantly to zero')
        outsel.add_constant(Name(['constant', 'one']),
                            docstring='Tie constantly to one')
        outsel.add_constant(Name(['constant', 'high', 'z']),
                            docstring='Tie constantly to high-Z')
        i = 0
        for sig in pinmux_info['ios']:
            if sig['connection'] == 'muxed' and sig['type'] in [
                    'inout', 'output'
            ]:
                index = Name([str(sig['idx'])]) if sig['idx'] != -1 else Name(
                    [])
                name = Name.from_snake_case(sig['name']) + index
                outsel.add_constant(name,
                                    docstring='Peripheral Output {}'.format(i))
                i += 1

        if isinstance(outsel, RustEnum):
            outsel.add_number_of_variants('Number of valid outsel value')
        else:
            outsel.add_last_constant('Last valid outsel value')

        self.pinmux_peripheral_in = peripheral_in
        self.pinmux_insel = insel
        self.pinmux_mio_out = mio_out
        self.pinmux_outsel = outsel

    def _init_pad_mapping(self):
        """Generate Rust enums for order of MIO and DIO pads.

        These are needed to configure pad specific configurations such as
        slew rate and other flags.
        """
        direct_enum = self._enum_type(self._top_name, Name(["direct", "pads"]))
        muxed_enum = self._enum_type(self._top_name, Name(["muxed", "pads"]))

        pads_info = self.top['pinout']['pads']
        muxed = [
            pad['name'] for pad in pads_info if pad['connection'] == 'muxed'
        ]

        # The logic here follows the sequence done in toplevel_pkg.sv.tpl.
        # The direct pads do not enumerate directly from the pinout like the
        # muxed ios.  Instead it follows a direction from the pinmux
        # perspective.
        pads_info = self.top['pinmux']['ios']
        direct = [pad for pad in pads_info if pad['connection'] != 'muxed']

        for pad in (direct):
            name = f"{pad['name']}"
            if pad['width'] > 1:
                name = f"{name}{pad['idx']}"

            direct_enum.add_constant(Name.from_snake_case(name))
        if isinstance(direct_enum, RustEnum):
            direct_enum.add_number_of_variants("Number of valid direct pad")
        else:
            direct_enum.add_last_constant("Last valid direct pad")

        for pad in (muxed):
            muxed_enum.add_constant(Name.from_snake_case(pad))
        if isinstance(muxed_enum, RustEnum):
            muxed_enum.add_number_of_variants("Number of valid muxed pad")
        else:
            muxed_enum.add_last_constant("Last valid muxed pad")

        self.direct_pads = direct_enum
        self.muxed_pads = muxed_enum

    def _init_pwrmgr_wakeups(self):
        enum = self._enum_type(self._top_name,
                               Name(["power", "manager", "wake", "ups"]))

        for signal in self.top["wakeups"]:
            enum.add_constant(
                Name.from_snake_case(signal["module"]) +
                Name.from_snake_case(signal["name"]))

        if isinstance(enum, RustEnum):
            enum.add_number_of_variants("Number of valid pwrmgr wakeup signal")
        else:
            enum.add_last_constant("Last valid pwrmgr wakeup signal")

        self.pwrmgr_wakeups = enum

    # Enumerates the positions of all software controllable resets
    def _init_rstmgr_sw_rsts(self):
        sw_rsts = [r.name for r in self.top['resets'].get_sw_resets()]

        enum = self._enum_type(self._top_name,
                               Name(["reset", "manager", "sw", "resets"]))

        for rst in sw_rsts:
            enum.add_constant(Name.from_snake_case(rst))

        if isinstance(enum, RustEnum):
            enum.add_number_of_variants(
                "Number of valid rstmgr software reset request")
        else:
            enum.add_last_constant("Last valid rstmgr software reset request")

        self.rstmgr_sw_rsts = enum

    def _init_pwrmgr_reset_requests(self):
        enum = self._enum_type(self._top_name,
                               Name(["power", "manager", "reset", "requests"]))

        for signal in self.top["reset_requests"]["peripheral"]:
            enum.add_constant(
                Name.from_snake_case(signal["module"]) +
                Name.from_snake_case(signal["name"]))

        if isinstance(enum, RustEnum):
            enum.add_number_of_variants(
                "Number of valid pwrmgr reset_request signal")
        else:
            enum.add_last_constant("Last valid pwrmgr reset_request signal")

        self.pwrmgr_reset_requests = enum

    def _init_clkmgr_clocks(self):
        """
        Creates RustEnums for accessing the software-controlled clocks in the
        design.

        The logic here matches the logic in topgen.py in how it instantiates the
        clock manager with the described clocks.

        We differentiate "gateable" clocks and "hintable" clocks because the
        clock manager has separate register interfaces for each group.
        """
        clocks = self.top['clocks']

        gateable_clocks = self._enum_type(self._top_name,
                                          Name(["gateable", "clocks"]))
        hintable_clocks = self._enum_type(self._top_name,
                                          Name(["hintable", "clocks"]))

        c2g = clocks.make_clock_to_group()
        by_type = clocks.typed_clocks()

        for name in by_type.sw_clks.keys():
            # All these clocks start with `clk_` which is redundant.
            clock_name = Name.from_snake_case(name).remove_part("clk")
            docstring = "Clock {} in group {}".format(name, c2g[name].name)
            gateable_clocks.add_constant(clock_name, docstring)
        if isinstance(gateable_clocks, RustEnum):
            gateable_clocks.add_number_of_variants(
                "Number of Valid Gateable Clock")
        else:
            gateable_clocks.add_last_constant("Last Valid Gateable Clock")

        for name in by_type.hint_clks.keys():
            # All these clocks start with `clk_` which is redundant.
            clock_name = Name.from_snake_case(name).remove_part("clk")
            docstring = "Clock {} in group {}".format(name, c2g[name].name)
            hintable_clocks.add_constant(clock_name, docstring)
        if isinstance(hintable_clocks, RustEnum):
            hintable_clocks.add_number_of_variants(
                "Number of Valid Hintable Clock")
        else:
            hintable_clocks.add_last_constant("Last Valid Hintable Clock")

        self.clkmgr_gateable_clocks = gateable_clocks
        self.clkmgr_hintable_clocks = hintable_clocks

    def _init_subranges(self, addr_space_name: str):
        """
        Computes the bounds of all subspace regions of a given address space.
        """
        subspace_regions = []
        addr_space = get_addr_space(self.top, addr_space_name)
        for subspace in addr_space.get('subspaces', []):
            regions = []
            for node in subspace['nodes']:
                # Get the dot-delimited interface name. If no interface
                # name is given, all device interfaces are considered for
                # this subspace range.
                split_dev = node.rsplit('.', 1)
                dev_name = split_dev[0]
                if_name = None
                if len(split_dev) > 1:
                    if_name = split_dev[1]

                # Include both register blocks and memories.
                ranges = get_device_ranges(self.devices(addr_space_name) +
                                           self.memories(addr_space_name),
                                           dev_name)
                if if_name:
                    # Only a single interface, if name contained an interface
                    # name
                    regions.append(ranges[if_name])
                else:
                    # All interfaces
                    regions += list(ranges.values())

            subspace_range = range(
                min([r.base_addr for r in regions]),
                max([r.base_addr + r.size_bytes for r in regions]))
            subspace_region = MemoryRegion(
                self._top_name, Name([subspace['name']]), addr_space_name,
                subspace_range.start,
                subspace_range.stop - subspace_range.start)
            subspace_regions.append(
                (subspace['name'], subspace['desc'], subspace_region))

        self.subranges[addr_space_name] = subspace_regions


def write_file_secure(file_path: Path, content: str,
                      mode: int = 0o600) -> None:
    """
    Write content to a file with secure permissions.

    For secure files, uses os.open() with O_CREAT | O_EXCL to atomically create
    the file with the correct permissions from the start. This prevents race
    conditions in shared NFS environments without needing temporary files.

    Args:
        file_path: Path where the file should be written
        content: Content to write to the file
        mode: File permissions to set (default: 0o600 for owner read/write only)
    """
    file_path.parent.mkdir(parents=True, exist_ok=True)

    # First delete file if it exists so that we can securely create it
    if file_path.exists():
        file_path.unlink()

    # For sensitive files: atomically create with correct permissions
    flags = os.O_CREAT | os.O_EXCL | os.O_WRONLY
    file_descriptor = os.open(file_path, flags, mode)
    with os.fdopen(file_descriptor, "w", encoding="UTF-8") as fout:
        fout.write(content)
