#!/usr/bin/env python3
# Copyright 2017-2020 The Verible Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Print module name, ports, parameters and imports.

Usage: print_modules.py PATH_TO_VERIBLE_VERILOG_SYNTAX \\
                        VERILOG_FILE [VERILOG_FILE [...]]

This example shows how to use ``verible-verilog-syntax --export_json ...``
output to extract information about module declarations found in System Verilog
source files. Extracted information:

* module name
* module port names
* module parameter names
* module imports
* module header code
"""

import sys

import anytree

import verible_verilog_syntax


def process_file_data(path: str, data: verible_verilog_syntax.SyntaxData):
  """Print information about modules found in SystemVerilog file.

  This function uses verible_verilog_syntax.Node methods to find module
  declarations and specific tokens containing following information:

  * module name
  * module port names
  * module parameter names
  * module imports
  * module header code

  Args:
    path: Path to source file (used only for informational purposes)
    data: Parsing results returned by one of VeribleVerilogSyntax' parse_*
          methods.
  """
  if not data.tree:
    return

  modules_info = []

  # Collect information about each module declaration in the file
  for module in data.tree.iter_find_all({"tag": "kModuleDeclaration"}):
    module_info = {
      "header_text": "",
      "name": "",
      "ports": [],
      "parameters": [],
      "imports": [],
    }

    # Find module header
    header = module.find({"tag": "kModuleHeader"})
    if not header:
      continue
    module_info["header_text"] = header.text

    # Find module name
    name = header.find({"tag": ["SymbolIdentifier", "EscapedIdentifier"]},
                        iter_=anytree.PreOrderIter)
    if not name:
      continue
    module_info["name"] = name.text

    # Get the list of ports
    for port in header.iter_find_all({"tag": ["kPortDeclaration", "kPort"]}):
      port_id = port.find({"tag": ["SymbolIdentifier", "EscapedIdentifier"]})
      module_info["ports"].append(port_id.text)

    # Get the list of parameters
    for param in header.iter_find_all({"tag": ["kParamDeclaration"]}):
      param_id = param.find({"tag": ["SymbolIdentifier", "EscapedIdentifier"]})
      module_info["parameters"].append(param_id.text)

    # Get the list of imports
    for pkg in module.iter_find_all({"tag": ["kPackageImportItem"]}):
      module_info["imports"].append(pkg.text)

    modules_info.append(module_info)

  # Print results
  if len(modules_info) > 0:
    print(f"\033[1;97;7m{path} \033[0m\n")

  def print_entry(key, values):
    fmt_values = [f"\033[92m{v}\033[0m" for v in values]
    value_part = (f"\n\033[33m// {' '*len(key)}".join(fmt_values)
                  or "\033[90m-\033[0m")
    print(f"\033[33m// \033[93m{key}{value_part}")

  for module_info in modules_info:
    print_entry("name:       ", [module_info["name"]])
    print_entry("ports:      ", module_info["ports"])
    print_entry("parameters: ", module_info["parameters"])
    print_entry("imports:    ", module_info["imports"])
    print(f"\033[97m{module_info['header_text']}\033[0m\n")


def main():
  if len(sys.argv) < 3:
    print(f"Usage: {sys.argv[0]} PATH_TO_VERIBLE_VERILOG_SYNTAX " +
          "VERILOG_FILE [VERILOG_FILE [...]]")
    return 1

  parser_path = sys.argv[1]
  files = sys.argv[2:]

  parser = verible_verilog_syntax.VeribleVerilogSyntax(executable=parser_path)
  data = parser.parse_files(files)

  for file_path, file_data in data.items():
    process_file_data(file_path, file_data)


if __name__ == "__main__":
  sys.exit(main())
