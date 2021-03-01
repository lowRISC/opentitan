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
"""VeribleVerilogSyntax test"""


import sys
import tempfile
import unittest

import verible_verilog_syntax


class VeribleVerilogSyntaxTest(unittest.TestCase):
  def setUp(self):
    if len(sys.argv) > 1:
      self.parser = verible_verilog_syntax.VeribleVerilogSyntax(
                                              executable=sys.argv[1])
    else:
      self.parser = verible_verilog_syntax.VeribleVerilogSyntax()

    self.assertIsNotNone(self.parser)

  def create_temp_file(self, content):
    tmp = tempfile.NamedTemporaryFile(mode="w", suffix=".sv")
    tmp.write(content)
    tmp.flush()
    return tmp


class TestParseMethods(VeribleVerilogSyntaxTest):
  def test_parse_string(self):
    data = self.parser.parse_string("module X(); endmodule;")
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.tree)
    self.assertIsNone(data.errors)

  def test_parse_string_with_all_options(self):
    data = self.parser.parse_string("module X(); endmodule;", options={
      "gen_tree": True,
      "gen_tokens": True,
      "gen_rawtokens": True,
    })
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.tree)
    self.assertIsNotNone(data.tokens)
    self.assertIsNotNone(data.rawtokens)
    self.assertIsNone(data.errors)

  def test_parse_string_error(self):
    data = self.parser.parse_string("endmodule X(); module;")
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.errors)

  def test_parse_file(self):
    file_ = self.create_temp_file("module X(); endmodule;")
    data = self.parser.parse_file(file_.name)
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.tree)
    self.assertIsNone(data.errors)

  def test_parse_file_with_all_options(self):
    file_ = self.create_temp_file("module X(); endmodule;")
    data = self.parser.parse_file(file_.name, options={
      "gen_tree": True,
      "gen_tokens": True,
      "gen_rawtokens": True,
    })
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.tree)
    self.assertIsNotNone(data.tokens)
    self.assertIsNotNone(data.rawtokens)
    self.assertIsNone(data.errors)

  def test_parse_file_error(self):
    file_ = self.create_temp_file("endmodule X(); module;")
    data = self.parser.parse_file(file_.name)
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.errors)

  def test_parse_files(self):
    files = [
      self.create_temp_file("module X(); endmodule;"),
      self.create_temp_file("module Y(); endmodule;"),
    ]
    data = self.parser.parse_files([f.name for f in files])
    self.assertIsNotNone(data)
    for f in files:
      self.assertIsNotNone(data[f.name])
      self.assertIsNotNone(data[f.name].tree)
      self.assertIsNone(data[f.name].errors)

  def test_parse_files_with_all_options(self):
    files = [
      self.create_temp_file("module X(); endmodule;"),
      self.create_temp_file("module Y(); endmodule;"),
    ]
    data = self.parser.parse_files([f.name for f in files], options={
      "gen_tree": True,
      "gen_tokens": True,
      "gen_rawtokens": True,
    })
    self.assertIsNotNone(data)
    for f in files:
      self.assertIsNotNone(data[f.name])
      self.assertIsNotNone(data[f.name].tree)
      self.assertIsNotNone(data[f.name].tokens)
      self.assertIsNotNone(data[f.name].rawtokens)
      self.assertIsNone(data[f.name].errors)

  def test_parse_files_error(self):
    # One file with, and one without errors
    files = [
      self.create_temp_file("endmodule X(); module;"),
      self.create_temp_file("module Y(); endmodule;"),
    ]
    data = self.parser.parse_files([f.name for f in files])
    self.assertIsNotNone(data)
    for f in files:
      self.assertIsNotNone(data[f.name])

    self.assertIsNotNone(data[files[0].name].errors)
    self.assertIsNone(data[files[1].name].errors)


class TestTree(VeribleVerilogSyntaxTest):
  def setUp(self):
    super().setUp()
    data = self.parser.parse_string(
        "module ModuleName#(parameter PARAM_NAME=42)\n" +
        "    (input portIn, output portOut);\n" +
        "  import import_pkg_name::*;\n" +
        "  wire wireName;\n" +
        "endmodule;\n" +
        "module OtherModule; endmodule;\n")
    self.assertIsNotNone(data)
    self.assertIsNotNone(data.tree)
    self.tree = data.tree

  def test_find(self):
    header = self.tree.find({"tag": "kModuleHeader"})
    self.assertIsNotNone(header)
    module_name = header.find({"tag": "SymbolIdentifier"})
    self.assertIsNotNone(module_name)
    self.assertEqual(module_name.text, "ModuleName")
    nonexistent = header.find({"tag": "SomeUndefinedTag"})
    self.assertIsNone(nonexistent)

  def test_find_all(self):
    headers = self.tree.find_all({"tag": "kModuleHeader"})
    self.assertEqual(len(headers), 2)

    identifiers = self.tree.find_all({"tag": "SymbolIdentifier"})
    self.assertEqual(len(identifiers), 7)

    some_identifiers = self.tree.find_all({"tag": "SymbolIdentifier"},
                                          max_count=4)
    self.assertEqual(len(some_identifiers), 4)

  def test_iter_find_all(self):
    identifiers = [n.text
                   for n
                   in self.tree.iter_find_all({"tag": "SymbolIdentifier"})]
    self.assertIn("ModuleName", identifiers)
    self.assertIn("PARAM_NAME", identifiers)
    self.assertIn("OtherModule", identifiers)

  def test_custom_filter(self):
    def tokens_past_135_byte(node):
      return (isinstance(node, verible_verilog_syntax.TokenNode)
              and node.start > 135)

    other_module_tokens = self.tree.find_all(tokens_past_135_byte)
    self.assertGreaterEqual(len(other_module_tokens), 5)
    for token in other_module_tokens:
      self.assertGreater(token.start, 135)

  def test_search_order(self):
    level_order = self.tree.find_all({"tag": "SymbolIdentifier"})
    depth_order = self.tree.find_all({"tag": "SymbolIdentifier"},
                              iter_=verible_verilog_syntax.PreOrderTreeIterator)

    def check_items_order(iterable, items_to_check):
      index = 0
      for item in iterable:
        if items_to_check[index] == item:
          index += 1
        if index == len(items_to_check):
          return True
      return False

    self.assertTrue(check_items_order([n.text for n in level_order],
                                      ["ModuleName", "OtherModule", "portIn"]))
    self.assertTrue(check_items_order([n.text for n in depth_order],
                                      ["ModuleName", "portIn", "OtherModule"]))

  def test_node_properties(self):
    header = self.tree.find({"tag": "kModuleHeader"})
    self.assertIsNotNone(header)

    module_kw = header.find({"tag": "module"})
    self.assertEqual(module_kw.text, "module")
    self.assertEqual(module_kw.start, 0)
    self.assertEqual(module_kw.end, 6)

    semicolon = header.find({"tag": ";"})
    self.assertEqual(semicolon.text, ";")
    self.assertEqual(semicolon.start, 78)
    self.assertEqual(semicolon.end, 79)

    self.assertEqual(header.start, module_kw.start)
    self.assertEqual(header.end, semicolon.end)
    self.assertTrue(header.text.startswith("module"))
    self.assertTrue(header.text.endswith(");"))


class TestTokens(VeribleVerilogSyntaxTest):
  def test_tokens(self):
    data = self.parser.parse_string(
          "module X(input portIn, output portOut); endmodule;", options={
      "gen_tree": False,
      "gen_tokens": True,
    })

    self.assertIsNotNone(data)
    self.assertIsNotNone(data.tokens)

    identifiers = [t for t in data.tokens if t.tag == "SymbolIdentifier"]

    module_name = identifiers[0]
    self.assertEqual(module_name.text, "X")
    self.assertEqual(module_name.start, 7)
    self.assertEqual(module_name.end, 8)

    texts = [t.text for t in identifiers]
    self.assertSequenceEqual(texts, ["X", "portIn", "portOut"])


  def test_rawtokens(self):
    data = self.parser.parse_string(
          "module X(input portIn, output portOut); endmodule;", options={
      "gen_tree": False,
      "gen_rawtokens": True,
    })

    self.assertIsNotNone(data)
    self.assertIsNotNone(data.rawtokens)

    identifiers = [t for t in data.rawtokens if t.tag == "SymbolIdentifier"]

    module_name = identifiers[0]
    self.assertEqual(module_name.text, "X")
    self.assertEqual(module_name.start, 7)
    self.assertEqual(module_name.end, 8)

    texts = [t.text for t in identifiers]
    self.assertSequenceEqual(texts, ["X", "portIn", "portOut"])


if __name__ == "__main__":
  unittest.main(argv=sys.argv[0:1], verbosity=2)
