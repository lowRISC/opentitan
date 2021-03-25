# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import re
import shutil
import sys

import yaml
from mako.template import Template

try:
    from yaml import CSafeLoader as YamlLoader, CSafeDumper as YamlDumper
except ImportError:
    from yaml import SafeLoader as YamlLoader, SafeDumper as YamlDumper


def _split_vlnv(core_vlnv):
    (vendor, library, name, version) = core_vlnv.split(':', 4)
    return {
        'vendor': vendor,
        'library': library,
        'name': name,
        'version': version
    }


def _prim_cores(cores, prim_name=None):
    """ Get all cores of primitives found by fusesoc

    If prim_name is given, only primitives with the given name are returned.
    Otherwise, all primitives are returned, independent of their name.
    """
    def _filter_primitives(core):
        """ Filter a list of cores to find the primitives we're interested in

        Matching cores follow the pattern
        "lowrisc:prim_<TECHLIB_NAME>:<PRIM_NAME>", where "<TECHLIB_NAME>" and
        "<PRIM_NAME>" are placeholders.
        """

        vlnv = _split_vlnv(core[0])
        if (vlnv['vendor'] == 'lowrisc' and
                vlnv['library'].startswith('prim_') and
            (prim_name is None or vlnv['name'] == prim_name)):

            return core
        return None

    return dict(filter(_filter_primitives, cores.items()))


def _techlibs(prim_cores):
    techlibs = set()
    for name, info in prim_cores.items():
        vlnv = _split_vlnv(name)
        techlibs.add(_library_to_techlib_name(vlnv['library']))
    return techlibs


def _library_to_techlib_name(library):
    return library[len("prim_"):]


def _core_info_for_techlib(prim_cores, techlib):
    for name, info in prim_cores.items():
        vlnv = _split_vlnv(name)
        if _library_to_techlib_name(vlnv['library']) == techlib:
            return (name, info)


def _enum_name_for_techlib(techlib_name, qualified=True):
    name = "Impl" + techlib_name.capitalize()
    if qualified:
        name = "prim_pkg::" + name
    return name


def _top_module_file(core_files, module_name):
    module_filename = module_name + '.sv'
    for file in core_files:
        if os.path.basename(file) == module_filename:
            return file


def _parse_module_header(generic_impl_filepath, module_name):
    """ Parse a SystemVerilog file to extract the 'module' header

    Return a dict with the following entries:
    - module_header: the whole module header (including the 'module' keyword)
    - package_import_declaration: import declarations
    - parameter_port_list: parameter/localparam declarations in the header
    - ports: the list of ports. The portlist can be ANSI or non-ANSI style (with
      or without signal declarations; see the SV spec for details).
    """

    # TODO: Evaluate different Python SV parsers and use one instead of this
    # beautiful regex. A more complete parser would ignore comments, for
    # example, or properly handle matching parentheses ... Or write a minimal
    # parser that can parse the module header.
    #
    # Initial evaluations:
    # - https://github.com/PyHDI/Pyverilog:
    #   requires Icarus and Python 3.6
    # - https://kevinpt.github.io/hdlparse/:
    #   Didn't do anything in my tests.
    # - https://github.com/sepandhaghighi/verilogparser:
    #   Doesn't support SystemVerilog

    # Grammar fragments from the SV2017 spec:
    #
    # module_nonansi_header ::=
    #   { attribute_instance } module_keyword [ lifetime ] module_identifier
    #   { package_import_declaration } [ parameter_port_list ] list_of_ports ;
    # module_ansi_header ::=
    #   { attribute_instance } module_keyword [ lifetime ] module_identifier
    #   { package_import_declaration }1 [ parameter_port_list ] [ list_of_port_declarations ]
    # package_import_declaration ::=
    #   import package_import_item { , package_import_item } ;
    # package_import_item ::=
    #   package_identifier :: identifier
    #   | package_identifier :: *

    RE_MODULE_HEADER = (
        r'(?:\s|^)'
        r'(?P<module_header>'  # start: capture the whole module header
        r'module\s+'  # module_keyword
        r'(?:(?:static|automatic)\s+)?'  # lifetime (optional)
        + module_name +  # module_identifier
        r'\s*(?P<package_import_declaration>(?:import\s+[^;]+;)+)?'  # package_import_declaration (optional, skipped)
        r'\s*(?:#\s*\((?P<parameter_port_list>[^;]+)\))?'  # parameter_port_list (optional)
        r'\s*\(\s*(?P<ports>[^;]+)\s*\)'  # list_of_port_declarations or list_of_ports
        r'\s*;'  # trailing semicolon
        r')'  # end: capture the whole module header
    )

    data = ""
    with open(generic_impl_filepath, encoding="utf-8") as file:
        data = file.read()
    re_module_header = re.compile(RE_MODULE_HEADER, re.DOTALL)
    matches = re_module_header.search(data)
    if not matches:
        raise ValueError("Unable to extract module header from %s." %
                         (generic_impl_filepath, ))

    parameter_port_list = matches.group('parameter_port_list') or ''
    return {
        'module_header':
        matches.group('module_header').strip(),
        'package_import_declaration':
        matches.group('package_import_declaration') or '',
        'parameter_port_list':
        parameter_port_list,
        'ports':
        matches.group('ports').strip() or '',
        'parameters':
        _parse_parameter_port_list(parameter_port_list)
    }


def test_parse_parameter_port_list():
    assert _parse_parameter_port_list("parameter enum_t P") == {'P'}
    assert _parse_parameter_port_list("parameter integer P") == {'P'}
    assert _parse_parameter_port_list("parameter logic [W-1:0] P") == {'P'}
    assert _parse_parameter_port_list("parameter logic [W-1:0] P = '0") == {'P'}
    assert _parse_parameter_port_list("parameter logic [W-1:0] P = 'b0") == {'P'}
    assert _parse_parameter_port_list("parameter logic [W-1:0] P = 2'd0") == {'P'}


def _parse_parameter_port_list(parameter_port_list):
    """ Parse a list of ports in a module header into individual parameters """

    # Grammar (SV2017):
    #
    # parameter_port_list ::=
    #     # ( list_of_param_assignments { , parameter_port_declaration } )
    #   | # ( parameter_port_declaration { , parameter_port_declaration } )
    #   | #( )
    # parameter_port_declaration ::=
    #   parameter_declaration
    #   | local_parameter_declaration
    #   | data_type list_of_param_assignments
    #   | type list_of_type_assignments

    # XXX: Not covering the complete grammar, e.g. `parameter x, y`
    RE_PARAMS = (
        r'parameter\s+'
        r'(?:[a-zA-Z0-9_\]\[:\s\$-]+\s+)?'  # type
        r'(?P<name>\w+)'  # name
        r'(?:\s*=\s*[^,;]+)?'  # initial value
    )
    re_params = re.compile(RE_PARAMS)
    parameters = set()
    for m in re_params.finditer(parameter_port_list):
        parameters.add(m.group('name'))
    return parameters


def _check_gapi(gapi):
    if 'cores' not in gapi:
        print("Key 'cores' not found in GAPI structure. "
              "Install a compatible version with "
              "'pip3 install --user -r python-requirements.txt'.")
        return False
    return True


def _generate_prim_pkg(gapi):
    all_prim_cores = _prim_cores(gapi['cores'])
    techlibs = _techlibs(all_prim_cores)

    techlib_enums = []

    # Insert the required generic library first to ensure it gets enum value 0
    techlib_enums.append(_enum_name_for_techlib('generic', qualified=False))

    for techlib in techlibs:
        if techlib == 'generic':
            # The generic implementation is required and handled separately.
            continue
        techlib_enums.append(_enum_name_for_techlib(techlib, qualified=False))

    # Render prim_pkg.sv file
    print("Creating prim_pkg.sv")
    prim_pkg_sv_tpl_filepath = os.path.join(os.path.dirname(__file__),
                                            'primgen', 'prim_pkg.sv.tpl')
    prim_pkg_sv_tpl = Template(filename=prim_pkg_sv_tpl_filepath)

    prim_pkg_sv = prim_pkg_sv_tpl.render(encoding="utf-8",
                                         techlib_enums=techlib_enums)
    with open('prim_pkg.sv', 'w') as f:
        f.write(prim_pkg_sv)

    # Copy prim_pkg.core (no changes needed)
    prim_pkg_core_src = os.path.join(os.path.dirname(__file__), 'primgen',
                                     'prim_pkg.core.tpl')
    prim_pkg_core_dest = 'prim_pkg.core'
    shutil.copyfile(prim_pkg_core_src, prim_pkg_core_dest)
    print("Core file written to %s." % (prim_pkg_core_dest, ))


def _instance_sv(prim_name, techlib, parameters):
    if not parameters:
        s = "    prim_{techlib}_{prim_name} u_impl_{techlib} (\n"
    else:
        s = "    prim_{techlib}_{prim_name} #(\n"
        s += ",\n".join("      .{p}({p})".format(p=p) for p in parameters)
        s += "\n    ) u_impl_{techlib} (\n"
    s += "      .*\n" \
         "    );\n"
    return s.format(prim_name=prim_name, techlib=techlib)


def _create_instances(prim_name, techlibs, parameters):
    """ Build SystemVerilog code instantiating primitives from the techlib """
    techlibs_wo_generic = [
        techlib for techlib in techlibs if techlib != 'generic'
    ]
    techlibs_generic_last = techlibs_wo_generic + ['generic']

    if not techlibs_wo_generic:
        # Don't output the if/else blocks if there no alternatives exist.
        # We still want the generate block to keep hierarchical path names
        # stable, even if more than one techlib is found.
        s = "  if (1) begin : gen_generic\n"
        s += _instance_sv(prim_name, "generic", parameters) + "\n"
        s += "  end"
        return s

    nr_techlibs = len(techlibs_generic_last)
    out = ""
    for pos, techlib in enumerate(techlibs_generic_last):
        is_first = pos == 0
        is_last = pos == nr_techlibs - 1

        s = ""
        if not is_first:
            s += "else "
        if not is_last:
            s += "if (Impl == {techlib_enum}) "

        # TODO: wildcard port lists are against our style guide, but it's safer
        # to let the synthesis tool figure out the connectivity than us trying
        # to parse the port list into individual signals.
        s += "begin : gen_{techlib}\n" + _instance_sv(prim_name, techlib,
                                                      parameters) + "end"

        if not is_last:
            s += " "

        out += s.format(prim_name=prim_name,
                        techlib=techlib,
                        techlib_enum=_enum_name_for_techlib(techlib))
    return out


def _generate_abstract_impl(gapi):
    prim_name = gapi['parameters']['prim_name']
    prim_cores = _prim_cores(gapi['cores'], prim_name)

    techlibs = _techlibs(prim_cores)

    if 'generic' not in techlibs:
        raise ValueError("Techlib generic is required, but not found for "
                         "primitive %s." % prim_name)
    print("Implementations for primitive %s: %s" %
          (prim_name, ', '.join(techlibs)))

    # Extract port list out of generic implementation
    generic_core = _core_info_for_techlib(prim_cores, 'generic')[1]
    generic_module_name = 'prim_generic_' + prim_name
    top_module_filename = _top_module_file(generic_core['files'],
                                           generic_module_name)
    top_module_file = os.path.join(generic_core['core_root'],
                                   top_module_filename)

    print("Inspecting generic module %s" % (top_module_file, ))
    generic_hdr = _parse_module_header(top_module_file, generic_module_name)

    # Render abstract primitive HDL from template
    print("Creating SystemVerilog module for abstract primitive")
    abstract_prim_sv_tpl_filepath = os.path.join(os.path.dirname(__file__),
                                                 'primgen',
                                                 'abstract_prim.sv.tpl')
    abstract_prim_sv_tpl = Template(filename=abstract_prim_sv_tpl_filepath)

    abstract_prim_sv = abstract_prim_sv_tpl.render(
        encoding="utf-8",
        prim_name=prim_name,
        module_header_imports=generic_hdr['package_import_declaration'],
        module_header_params=generic_hdr['parameter_port_list'],
        module_header_ports=generic_hdr['ports'],
        num_techlibs= len(techlibs),
        # Creating the code to instantiate the primitives in the Mako templating
        # language is tricky to do; do it in Python instead.
        instances=_create_instances(prim_name, techlibs,
                                    generic_hdr['parameters']))
    abstract_prim_sv_filepath = 'prim_%s.sv' % (prim_name)
    with open(abstract_prim_sv_filepath, 'w') as f:
        f.write(abstract_prim_sv)
    print("Abstract primitive written to %s" %
          (os.path.abspath(abstract_prim_sv_filepath), ))

    # Create core file depending on all primitive implementations we have in the
    # techlibs.
    print("Creating core file for primitive %s." % (prim_name, ))
    abstract_prim_core_filepath = os.path.abspath('prim_%s.core' % (prim_name))
    dependencies = []
    dependencies.append('lowrisc:prim:prim_pkg')
    dependencies += [
        _core_info_for_techlib(prim_cores, t)[0] for t in techlibs
    ]
    abstract_prim_core = {
        'name': "lowrisc:prim_abstract:%s" % (prim_name, ),
        'filesets': {
            'files_rtl': {
                'depend': dependencies,
                'files': [
                    abstract_prim_sv_filepath,
                ],
                'file_type': 'systemVerilogSource'
            },
        },
        'targets': {
            'default': {
                'filesets': [
                    'files_rtl',
                ],
            },
        },
    }
    with open(abstract_prim_core_filepath, 'w') as f:
        # FuseSoC requires this line to appear first in the YAML file.
        # Inserting this line through the YAML serializer requires ordered dicts
        # to be used everywhere, which is annoying syntax-wise on Python <3.7,
        # where native dicts are not sorted.
        f.write('CAPI=2:\n')
        yaml.dump(abstract_prim_core,
                  f,
                  encoding="utf-8",
                  Dumper=YamlDumper)
    print("Core file written to %s" % (abstract_prim_core_filepath, ))


def _get_action_from_gapi(gapi, default_action):
    if 'parameters' in gapi and 'action' in gapi['parameters']:
        return gapi['parameters']['action']
    return default_action


def main():
    gapi_filepath = sys.argv[1]
    with open(gapi_filepath) as f:
        gapi = yaml.load(f, Loader=YamlLoader)

    if not _check_gapi(gapi):
        sys.exit(1)

    action = _get_action_from_gapi(gapi, 'generate_abstract_impl')

    if action == 'generate_abstract_impl':
        return _generate_abstract_impl(gapi)
    elif action == 'generate_prim_pkg':
        return _generate_prim_pkg(gapi)
    else:
        raise ValueError("Invalid action: %s" % (action, ))


if __name__ == '__main__':
    main()
