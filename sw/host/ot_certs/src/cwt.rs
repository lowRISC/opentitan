// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;
use std::fs;
use std::iter;
use std::path::PathBuf;

use crate::cbor;
use crate::codegen::Codegen;
use anyhow::{bail, Context, Result};
use heck::{ToShoutySnakeCase, ToUpperCamelCase};
use indexmap::IndexMap;
use itertools::Itertools;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CwtTemplate {
    /// Name of the certificate.
    pub name: String,
    /// Variable declarations.
    pub variables: IndexMap<String, TemplateVariable>,
    /// Constant declarations.
    pub constants: IndexMap<String, TemplateConstant>,
    /// Structure specification.
    pub structure: TemplateStructure,
}

#[derive(Clone, Copy, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum VariableSize {
    /// The maximum size of the variable.
    MaxSize(u64),
    /// The exact size of the variable.
    ExactSize(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum VariableType {
    /// Raw array of bytes.
    ByteArray,
    /// UTF-8 encoded string.
    String,
    /// Signed 64-bit integer.
    Integer,
}

/// Used to parse the variables defined in the template.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum TemplateVariable {
    /// Byte-array variable.
    ByteArray {
        #[serde(flatten)]
        size: VariableSize,
    },
    /// String variable.
    String {
        #[serde(flatten)]
        size: VariableSize,
    },
    /// Integer variable.
    Integer,
}

/// Used to parse the constants defined in the template.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum TemplateConstant {
    /// Byte-array constant.
    ByteArray {
        /// Big-endian hex-encoded bytes
        #[serde(with = "hex::serde")]
        value: Vec<u8>,
    },
    /// String constant.
    String { value: String },
    /// Integer constant.
    Integer { value: i64 },
}

/// Used to parse the structures defined in the template.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(untagged)]
pub enum TemplateStructure {
    /// A byte-array which encodes a CBOR structure.
    #[serde(rename_all = "kebab-case")]
    CborByteArray {
        cbor_byte_array: Box<TemplateStructure>,
    },
    /// An item is a variable or a constant.
    Item(String),
    /// A map that consists of key-value pairs.
    Map(IndexMap<String, TemplateStructure>),
    /// An array that consists of values.
    Array(Vec<TemplateStructure>),
}

// CodegenVar is used to unify the representation of TemplateVariable and TemplateConstant.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
struct CodegenVar {
    name: String,
    size: VariableSize,
    value: CodegenVarValue,
}

type CodegenVarTable = HashMap<String, CodegenVar>;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
enum CodegenVarValue {
    ByteArray(Option<Vec<u8>>),
    String(Option<String>),
    Integer(Option<i64>),
}

impl CodegenVar {
    fn from_template_variable(name: &str, var: &TemplateVariable) -> Result<Self> {
        let name = name.to_owned();
        let (size, value) = match var {
            TemplateVariable::ByteArray { size } => (*size, CodegenVarValue::ByteArray(None)),
            TemplateVariable::String { size } => (*size, CodegenVarValue::String(None)),
            TemplateVariable::Integer => (VariableSize::MaxSize(8), CodegenVarValue::Integer(None)),
        };

        Ok(Self { name, size, value })
    }

    fn from_template_constant(name: &str, var: &TemplateConstant) -> Result<Self> {
        let name = name.to_owned();
        let (value, size) = match var {
            TemplateConstant::ByteArray { value } => (
                CodegenVarValue::ByteArray(Some(value.clone())),
                VariableSize::ExactSize(value.len().try_into().with_context(|| {
                    format!("the size of {name} is too large for u64: {}", value.len())
                })?),
            ),
            TemplateConstant::String { value } => (
                CodegenVarValue::String(Some(value.clone())),
                VariableSize::ExactSize(value.len().try_into().with_context(|| {
                    format!("the size of {name} is too large for u64: {}", value.len())
                })?),
            ),
            TemplateConstant::Integer { value } => {
                let arg = if *value >= 0 { *value } else { -(*value + 1) } as u64;
                (
                    CodegenVarValue::Integer(Some(*value)),
                    VariableSize::ExactSize(cbor::arg_size(arg).0),
                )
            }
        };

        Ok(Self { name, size, value })
    }

    fn is_constant(&self) -> bool {
        match &self.value {
            CodegenVarValue::ByteArray(v) => v.is_some(),
            CodegenVarValue::String(v) => v.is_some(),
            CodegenVarValue::Integer(v) => v.is_some(),
        }
    }

    fn variable_type(&self) -> VariableType {
        match &self.value {
            CodegenVarValue::ByteArray(_) => VariableType::ByteArray,
            CodegenVarValue::String(_) => VariableType::String,
            CodegenVarValue::Integer(_) => VariableType::Integer,
        }
    }

    // Generate the input fields.
    fn declarations(&self, prefix: &str) -> String {
        assert!(!self.is_constant());

        match self.value {
            CodegenVarValue::ByteArray(_) => {
                indoc::formatdoc! { r#"
                    {prefix}uint8_t *{name};
                    {prefix}size_t {name}_size;
                    "#,
                    name = self.name
                }
            }
            CodegenVarValue::String(_) => {
                indoc::formatdoc! { r#"
                    {prefix}char *{name};
                    {prefix}size_t {name}_size;
                    "#,
                    name = self.name
                }
            }
            CodegenVarValue::Integer(_) => indoc::formatdoc! { r#"
                {prefix}int64_t {name};
                "#,
                name = self.name
            },
        }
    }

    // Generate the expression of the value.
    fn value_expression(&self) -> String {
        assert!(!self.is_constant());
        format!("values->{}", self.name)
    }

    // Generate the expression of the value size.
    fn size_expression(&self) -> String {
        assert!(!self.is_constant());
        if self.variable_type() != VariableType::Integer {
            format!("values->{}_size", self.name)
        } else {
            format!("cbor_calc_int_size(values->{})", self.name)
        }
    }
}

// CodegenStructure are stored inside a vector, and therefore we use indices to refer to other CodegenStructure.
// `Var` represents a leaf node, while others represent different types of internal nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
enum CodegenStructure<'a> {
    Var(&'a CodegenVar),
    CborByteArray(usize),
    Map(Vec<(usize, usize)>),
    Array(Vec<usize>),
}

impl CodegenStructure<'_> {
    fn from_template<'a>(
        template: &CwtTemplate,
        vars: &'a CodegenVarTable,
    ) -> Result<Vec<CodegenStructure<'a>>> {
        let mut nodes = Vec::<CodegenStructure>::new();
        let mut id_mapping = HashMap::<String, usize>::new();
        Self::build_codegen_structure(&template.structure, vars, &mut nodes, &mut id_mapping)
            .context("build_codegen_structure failed")?;
        Ok(nodes)
    }

    // Assign the indices in postorder.
    // For later size computations, we could just iterate the array without DFS,
    // because child nodes are always processed before their parent node.
    fn build_codegen_structure<'a>(
        cur: &TemplateStructure,
        vars: &'a CodegenVarTable,
        nodes: &mut Vec<CodegenStructure<'a>>,
        var_ids: &mut HashMap<String, usize>,
    ) -> Result<usize> {
        let node = match cur {
            TemplateStructure::Item(name) => {
                let var = vars
                    .get(name)
                    .with_context(|| format!("cannot find item {name} in template"))?;
                CodegenStructure::Var(var)
            }
            TemplateStructure::CborByteArray { cbor_byte_array } => {
                let inner = Self::build_codegen_structure(cbor_byte_array, vars, nodes, var_ids)?;
                CodegenStructure::CborByteArray(inner)
            }
            TemplateStructure::Map(items) => {
                let mut pairs = Vec::new();
                for (k, v) in items {
                    let item = TemplateStructure::Item(k.clone());
                    let first = Self::build_codegen_structure(&item, vars, nodes, var_ids)?;
                    let second = Self::build_codegen_structure(v, vars, nodes, var_ids)?;
                    pairs.push((first, second));
                }
                CodegenStructure::Map(pairs)
            }
            TemplateStructure::Array(items) => {
                let mut values = Vec::new();
                for item in items {
                    let value = Self::build_codegen_structure(item, vars, nodes, var_ids)?;
                    values.push(value);
                }
                CodegenStructure::Array(values)
            }
        };

        if let CodegenStructure::Var(var) = node {
            // Check if the node for this Var is created before.
            if var_ids.contains_key(&var.name) {
                // If so, just get its id and return.
                // This means that if a variable or a constant is used multiple times,
                // there will be exactly one node to represent it.
                Ok(var_ids[&var.name])
            } else {
                // Otherwise, create a new node, store its id in `var_ids` and return.
                let idx = nodes.len();
                nodes.push(node);
                var_ids.insert(var.name.clone(), idx);
                Ok(idx)
            }
        } else {
            // Always create a new node for it and return.
            let idx = nodes.len();
            nodes.push(node);
            Ok(idx)
        }
    }
}

// A CBOR data item (called `item` in the source code) consists of the following parts:
//
//   * major type (3 bit): the type of this data item
//
//   * additional information (5 bit): the information of `argument`
//
//   * argument: different meaning for different type
//
//               could be omitted if less than 24,
//               `additional information` will hold the actual value in this case
//
//   * content: the content of the data type
//
//
// |--------------------------------------------------------------|
// | major type | additional information | argument |   content   |
// |--------------------------------------------------------------|
//
// |-------------------------------------|
//                 1 byte
//                                       |----------|
//                                         arg_size
//                                                  |-------------|
//                                                   content_size
// |--------------------------------------------------------------|
//                            item_size
//
//
// Since we have CodegenStructure::CborByteArray, and there might be variables in the inner nodes,
// we need to compute the size of the whole inner structure before generating its CBOR.
//
// We define `content_size`, `arg_size` and `item_size` for each CodegenStructure,
// and represent them in `SizeExpression`.
//
// When the size of a given child item is known before runtime, it will be accumulated into the `constant` field.
// Otherwise, we could only know the exact size until runtime, and therefore we mark it in dependencies.
//
//
// The formulations are:
//
//   `content_size` = constant + `item_size`` of each dependent CodegenStructure, or
//                    constant + size expression of the CodegenVar
//
//   `item_size` = 1 + ArgSize::Constant + `content_size` or
//                 1 + encoded size of `content_size` + `content_size`
//
#[derive(Clone, Debug, PartialEq, Eq)]
struct SizeExpression<'a> {
    index: usize,
    arg_size: ArgSize,
    constant: u64,
    dependencies: SizeDependency<'a>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ArgSize {
    // Fixed size.
    Constant(u64),
    // Used for data types whose `argument` is its `content_size`.
    LengthOfContentSize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SizeDependency<'a> {
    Var(&'a CodegenVar),
    SubItemSize(Vec<usize>),
}

impl SizeExpression<'_> {
    // Return a SizeExpression whose `content_size` depends on a variable.
    fn from_codegenvar(index: usize, arg_size: ArgSize, var: &CodegenVar) -> SizeExpression<'_> {
        SizeExpression {
            index,
            arg_size,
            constant: 0,
            dependencies: SizeDependency::Var(var),
        }
    }

    // Return a SizeExpression with empty SubItemSize dependency.
    fn empty_dependency(index: usize, arg_size: ArgSize, constant: u64) -> Self {
        SizeExpression {
            index,
            arg_size,
            constant,
            dependencies: SizeDependency::SubItemSize(vec![]),
        }
    }

    fn add_constant(&mut self, constant: u64) {
        self.constant += constant;
    }

    fn add_dependency(&mut self, index: usize) {
        if let SizeDependency::SubItemSize(deps) = &mut self.dependencies {
            deps.push(index);
        } else {
            panic!("add_dependency should be only called on SizeExpression with SubItemSize dependency.")
        }
    }

    fn is_constant(&self) -> bool {
        match &self.dependencies {
            SizeDependency::Var(_) => false,
            SizeDependency::SubItemSize(items) => items.is_empty(),
        }
    }

    fn content_size(&self) -> u64 {
        assert!(self.is_constant());
        self.constant
    }

    fn item_size(&self) -> u64 {
        assert!(self.is_constant());
        match self.arg_size {
            ArgSize::Constant(arg) => 1 + arg + self.constant,
            ArgSize::LengthOfContentSize => 1 + cbor::arg_size(self.constant).0 + self.constant,
        }
    }

    // Generate the expression to compute `content_size`.
    fn content_size_expression(&self) -> String {
        let mut terms = Vec::new();

        if self.constant > 0 {
            terms.push(self.constant.to_string());
        }

        match &self.dependencies {
            SizeDependency::Var(var) => terms.push(var.size_expression()),
            SizeDependency::SubItemSize(items) => {
                terms.extend(items.iter().map(|idx| format!("item_size_{idx}")))
            }
        };

        itertools::Itertools::intersperse(terms.into_iter(), " + ".to_owned()).collect()
    }

    // Generate the expression to compute `item_size`.
    // If not a constant, the result expression will always depend on its `content_size`.
    fn item_size_expression(&self) -> String {
        if self.is_constant() {
            self.item_size().to_string()
        } else {
            match &self.arg_size {
                ArgSize::Constant(arg) => {
                    format!("{k} + content_size_{idx}", k = 1 + arg, idx = self.index)
                }
                ArgSize::LengthOfContentSize => format!(
                    "1 + cbor_calc_arg_size(content_size_{idx}) + content_size_{idx}",
                    idx = self.index
                ),
            }
        }
    }
}

// Derive the size expression of each CodegenStructure.
//
// `get_var_size` is used to query the exact size of CodegenVar.
// If the return value is None, it means that the size can't be determined until runtime.
//
// The reason to make this function as a parameter is that we currently have two scenarios:
//
//   1. get the exact size to generate the size computation code
//
//      `get_var_size` only returns a value when the size is exact.
//
//   2. get the maximum size of this structure
//
//      `get_var_size` always returns the maximum size.
fn derive_size_expressions<'a>(
    nodes: &'a [CodegenStructure],
    get_var_size: &impl Fn(&CodegenVar) -> Option<u64>,
) -> Result<Vec<SizeExpression<'a>>> {
    let mut exps = Vec::<SizeExpression>::new();

    // The items in the slice are alreay sorted in postorder.
    for (idx, node) in nodes.iter().enumerate() {
        // A helper function to generate a size expression from CodegenVar.
        let from_var = |arg_size, var| {
            if let Some(size) = get_var_size(var) {
                SizeExpression::empty_dependency(idx, arg_size, size)
            } else {
                SizeExpression::from_codegenvar(idx, arg_size, var)
            }
        };

        // A helper function to generate a size expression from dependent items.
        let from_deps = |arg_size, idxs: &mut dyn Iterator<Item = &usize>| {
            let mut exp = SizeExpression::empty_dependency(idx, arg_size, 0);
            for idx in idxs {
                let dep = &exps[*idx];
                if dep.is_constant() {
                    exp.add_constant(dep.item_size());
                } else {
                    exp.add_dependency(*idx);
                }
            }
            exp
        };

        let exp = match node {
            CodegenStructure::Var(var) => match var.variable_type() {
                VariableType::ByteArray => from_var(ArgSize::LengthOfContentSize, var),
                VariableType::String => from_var(ArgSize::LengthOfContentSize, var),
                VariableType::Integer => from_var(ArgSize::Constant(0), var),
            },
            CodegenStructure::CborByteArray(inner) => {
                from_deps(ArgSize::LengthOfContentSize, &mut iter::once(inner))
            }
            CodegenStructure::Map(items) => {
                let len = items.len().try_into().with_context(|| {
                    format!("the size of the map is too large for u64: {}", items.len())
                })?;
                from_deps(
                    ArgSize::Constant(cbor::arg_size(len).0),
                    &mut items.iter().flat_map(|(a, b)| [a, b]),
                )
            }
            CodegenStructure::Array(items) => {
                let len = items.len().try_into().with_context(|| {
                    format!(
                        "the size of the array is too large for u64: {}",
                        items.len()
                    )
                })?;
                from_deps(ArgSize::Constant(cbor::arg_size(len).0), &mut items.iter())
            }
        };

        exps.push(exp);
    }

    Ok(exps)
}

fn collect_codegenvar(template: &CwtTemplate) -> Result<CodegenVarTable> {
    let mut vars = HashMap::<String, CodegenVar>::new();

    for (name, var) in &template.variables {
        let ret = vars.insert(name.clone(), CodegenVar::from_template_variable(name, var)?);
        if ret.is_some() {
            bail!("A variable name {} already exists", name);
        }
    }

    for (name, var) in &template.constants {
        let ret = vars.insert(name.clone(), CodegenVar::from_template_constant(name, var)?);
        if ret.is_some() {
            bail!("A constant name {} already exists", name);
        }
    }

    Ok(vars)
}

// Generate the data members of the input structure.
fn generate_input_fields(vars: &CodegenVarTable, indent: &str) -> String {
    vars.iter()
        .filter(|(_, var)| !var.is_constant())
        .map(|(_, var)| var.declarations(indent))
        .collect()
}

// Generate the size computation code for each item whose size can't be determined until runtime.
fn generate_size_computations(size_exps: &[SizeExpression], prefix: &str) -> Result<String> {
    assert!(!size_exps.is_empty());

    let mut code = String::new();
    for size_exp in size_exps.iter().filter(|exp| !exp.is_constant()) {
        code += &format!(
            "{prefix}const size_t content_size_{} = {};\n",
            size_exp.index,
            size_exp.content_size_expression()
        );
        code += &format!(
            "{prefix}const size_t item_size_{} = {};\n",
            size_exp.index,
            size_exp.item_size_expression()
        );
    }

    Ok(code)
}

// Generate the code to check the sizes of input arguments.
// The first return value is used to check all input sizes.
// The second return value is used to check the final output size.
fn generate_size_checks(
    vars: &CodegenVarTable,
    whole_struct_size: &SizeExpression,
    prefix: &str,
) -> Result<(String, String)> {
    let mut input_checks = String::new();

    // Check the size of each input variable.
    for (_, var) in vars
        .iter()
        .filter(|(_, var)| !var.is_constant() && var.variable_type() != VariableType::Integer)
    {
        let size_exp = var.size_expression();
        let cond = match var.size {
            VariableSize::ExactSize(size) => format!("!= {size}"),
            VariableSize::MaxSize(size) => format!("> {size}"),
        };

        input_checks +=
            &format!("{prefix}if ({size_exp} {cond}) return kErrorCertInvalidArgument;\n");
    }

    let size_bound = if whole_struct_size.is_constant() {
        whole_struct_size.item_size().to_string()
    } else {
        format!("item_size_{idx}", idx = whole_struct_size.index)
    };

    // Check the input buffer size.
    input_checks +=
        &format!("{prefix}if (*inout_size < {size_bound}) return kErrorCertInvalidSize;\n");

    // Make sure that the output size is the same as calculated root `item_size`.
    let output_checks =
        format!("{prefix}if (*inout_size != {size_bound}) return kErrorCertInternal;\n");

    Ok((input_checks, output_checks))
}

fn collect_preorder_indicies_helper(nodes: &[CodegenStructure], root: usize, res: &mut Vec<usize>) {
    res.push(root);
    match &nodes[root] {
        CodegenStructure::Var(_) => {}
        CodegenStructure::CborByteArray(inner) => {
            collect_preorder_indicies_helper(nodes, *inner, res);
        }
        CodegenStructure::Map(items) => {
            for (k, v) in items {
                collect_preorder_indicies_helper(nodes, *k, res);
                collect_preorder_indicies_helper(nodes, *v, res);
            }
        }
        CodegenStructure::Array(items) => {
            for item in items {
                collect_preorder_indicies_helper(nodes, *item, res);
            }
        }
    }
}

fn collect_preorder_indicies(nodes: &[CodegenStructure]) -> Vec<usize> {
    let mut res = Vec::new();
    collect_preorder_indicies_helper(nodes, nodes.len() - 1, &mut res);
    res
}

// Each CodegenStructure maps to a CodeBlock.
type CodeBlock = Vec<GeneratedCode>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum GeneratedCode {
    // A single CBOR-function call.
    FunctionCall(String),
    // If all the arguments are constants, derive its resulting bytes directly.
    CborBytes(Vec<u8>),
}

struct GeneratedCborInstructions {
    constant_definitions: String,
    cbor_instructions: String,
}

fn generate_cbor_instructions(
    nodes: &[CodegenStructure],
    size_exps: &[SizeExpression],
    prefix: &str,
) -> Result<GeneratedCborInstructions> {
    assert!(nodes.len() == size_exps.len());

    let call_wrapper = |func_call: String| {
        indoc::formatdoc! { r#"
            {prefix}RETURN_IF_ERROR({func_call});
            "#
        }
    };

    let gen_inst = |inst: String| GeneratedCode::FunctionCall(call_wrapper(inst));

    // For each CodegenStructure, generate its CodeBlock first.
    let mut code_blocks = Vec::<CodeBlock>::new();
    for (idx, (node, size_exp)) in nodes.iter().zip(size_exps.iter()).enumerate() {
        let code_block = match node {
            CodegenStructure::Var(var) => match &var.value {
                CodegenVarValue::ByteArray(val) => {
                    let header = if let VariableSize::ExactSize(size) = var.size {
                        GeneratedCode::CborBytes(cbor::byte_array_header(size))
                    } else {
                        gen_inst(format!("cbor_write_bstr_header(&cbor, content_size_{idx})"))
                    };

                    let content = if let Some(constant) = val {
                        GeneratedCode::CborBytes(constant.clone())
                    } else {
                        let val = var.value_expression();
                        let size = var.size_expression();
                        gen_inst(format!("cbor_write_raw_bytes(&cbor, {val}, {size})"))
                    };

                    vec![header, content]
                }
                CodegenVarValue::String(val) => {
                    let header = if let VariableSize::ExactSize(size) = var.size {
                        GeneratedCode::CborBytes(cbor::string_header(size))
                    } else {
                        gen_inst(format!("cbor_write_tstr_header(&cbor, content_size_{idx})"))
                    };

                    let content = if let Some(constant) = val {
                        GeneratedCode::CborBytes(constant.as_bytes().to_vec())
                    } else {
                        let val = var.value_expression();
                        let size = var.size_expression();
                        gen_inst(format!(
                            "cbor_write_raw_bytes(&cbor, (uint8_t *){val}, {size})"
                        ))
                    };

                    vec![header, content]
                }
                CodegenVarValue::Integer(val) => match val {
                    Some(constant) => {
                        vec![GeneratedCode::CborBytes(cbor::int(*constant))]
                    }
                    None => {
                        let val = var.value_expression();
                        vec![gen_inst(format!("cbor_write_int(&cbor, {val})"))]
                    }
                },
            },
            CodegenStructure::CborByteArray(_) => {
                if size_exp.is_constant() {
                    let size = size_exp.content_size();
                    vec![GeneratedCode::CborBytes(cbor::byte_array_header(size))]
                } else {
                    vec![gen_inst(format!(
                        "cbor_write_bstr_header(&cbor, content_size_{idx})"
                    ))]
                }
            }
            CodegenStructure::Map(items) => {
                let len = items.len().try_into().with_context(|| {
                    format!("the size of the map is too large for u64: {}", items.len())
                })?;
                vec![GeneratedCode::CborBytes(cbor::map_header(len))]
            }
            CodegenStructure::Array(items) => {
                let len = items.len().try_into().with_context(|| {
                    format!(
                        "the size of the array is too large for u64: {}",
                        items.len()
                    )
                })?;
                vec![GeneratedCode::CborBytes(cbor::array_header(len))]
            }
        };

        code_blocks.push(code_block);
    }

    // Collect the code blocks, and then linearize them into a sequence of single operations.
    let order = collect_preorder_indicies(nodes);
    let insts = order.iter().flat_map(|&idx| code_blocks[idx].clone());

    let mut constant_definitions = String::new();
    let mut cbor_instructions = String::new();

    // For neighboring CBOR, we collect them into a single array and write them at once.
    let mut idx = 0usize;
    for (is_constant, chunk) in &insts.chunk_by(|inst| matches!(inst, GeneratedCode::CborBytes(_)))
    {
        if is_constant {
            let buf = chunk.flat_map(|inst| match inst {
                GeneratedCode::CborBytes(inner) => inner,
                _ => panic!("Shouldn't have any non GeneratedCode::CborBytes variant."),
            });

            let bytes = buf.map(|ch| format!("{}", ch));
            let initializer: String =
                itertools::Itertools::intersperse(bytes, ", ".to_owned()).collect();

            constant_definitions += &indoc::formatdoc! { r#"
                {prefix}const static uint8_t binary_{idx}[] = {{{initializer}}};
                "#};
            cbor_instructions += &call_wrapper(format!(
                "cbor_write_raw_bytes(&cbor, binary_{idx}, sizeof(binary_{idx}))"
            ));

            idx += 1;
        } else {
            for block in chunk {
                match block {
                    GeneratedCode::FunctionCall(inner) => cbor_instructions += &inner,
                    _ => panic!("Shouldn't have any non GeneratedCode::FunctionCall variant."),
                }
            }
        }
    }

    Ok(GeneratedCborInstructions {
        constant_definitions,
        cbor_instructions,
    })
}

fn generate_header(from_file: &str, template_name: &str, max_size: u64, decls: String) -> String {
    let preproc_guard_include = template_name.to_shouty_snake_case();
    let enum_name = template_name.to_upper_camel_case();

    indoc::formatdoc! { r#"
        // Copyright lowRISC contributors (OpenTitan project).
        // Licensed under the Apache License, Version 2.0, see LICENSE for details.
        // SPDX-License-Identifier: Apache-2.0

        // This file was automatically generated using opentitantool from:
        // {from_file}
        #ifndef __{preproc_guard_include}__
        #define __{preproc_guard_include}__

        #include "sw/device/lib/base/status.h"

        typedef struct {template_name}_values {{
        {decls}}} {template_name}_values_t;

        enum {{
          k{enum_name}MaxVariableSizeBytes = {max_size},
        }};

        rom_error_t {template_name}_build({template_name}_values_t *values, uint8_t *output, size_t *inout_size);

        #endif
    "#}
}

fn generate_source(
    from_file: &str,
    template_name: &str,
    constant_definitions: &str,
    size_computations: &str,
    input_size_checks: &str,
    output_size_checks: &str,
    cbor_instructions: &str,
) -> String {
    let source_template = indoc::formatdoc! { r#"
        // Copyright lowRISC contributors (OpenTitan project).
        // Licensed under the Apache License, Version 2.0, see LICENSE for details.
        // SPDX-License-Identifier: Apache-2.0

        // This file was automatically generated using opentitantool from:
        // {from_file}

        #include "{template_name}.h"
        #include "sw/device/silicon_creator/lib/cert/cbor.h"

        {constant_definitions}
        rom_error_t {template_name}_build({template_name}_values_t *values, uint8_t *buffer, size_t *inout_size) {{
        {size_computations}
        {input_size_checks}
          struct CborOut cbor;
          RETURN_IF_ERROR(cbor_write_out_init(&cbor, buffer, *inout_size));

        {cbor_instructions}
          *inout_size = CborOutSize(&cbor);
        {output_size_checks}
          return kErrorOk;
        }}
    "#};

    source_template
}

impl CwtTemplate {
    pub fn from_hjson_str(content: &str) -> Result<CwtTemplate> {
        deser_hjson::from_str(content).context("CwtTemplate::from_hjson_str failed")
    }
}

pub fn load_cwt_template(path: &PathBuf) -> Result<CwtTemplate> {
    let template_content = fs::read_to_string(path)
        .with_context(|| format!("could not load the template file {}", path.display()))?;

    CwtTemplate::from_hjson_str(&template_content).with_context(|| {
        format!(
            "failed to parse CwtTemplate from the template file {}",
            path.display()
        )
    })
}

pub fn generate_cert(from_file: &str, template: &CwtTemplate) -> Result<Codegen> {
    let vars = collect_codegenvar(template).context("collect_codegenvar failed")?;

    let structures = CodegenStructure::from_template(template, &vars)
        .context("CodegenStructure::from_template failed")?;

    let max_size = {
        let exp = derive_size_expressions(&structures, &|var| match var.size {
            VariableSize::ExactSize(size) => Some(size),
            VariableSize::MaxSize(size) => Some(size),
        })
        .context("derive_size_expressions for maximum size failed")?;

        exp.last()
            .context("there isn't any item in the structure")?
            .item_size()
    };

    let decls = generate_input_fields(&vars, "  ");

    let source_h = generate_header(from_file, &template.name, max_size, decls);

    let exact_sizes = derive_size_expressions(&structures, &|var| match var.size {
        VariableSize::ExactSize(size) => Some(size),
        _ => None,
    })
    .context("derive_size_expressions for exact size failed")?;

    let size_computations = generate_size_computations(&exact_sizes, "  ")
        .context("generate_size_computations failed")?;

    let (input_size_checks, output_size_checks) = generate_size_checks(
        &vars,
        exact_sizes
            .last()
            .context("there isn't any item in the structure")?,
        "  ",
    )
    .context("generate_size_checks failed")?;

    let GeneratedCborInstructions {
        constant_definitions,
        cbor_instructions,
    } = generate_cbor_instructions(&structures, &exact_sizes, "  ")
        .context("generate_cbor_instructions failed")?;

    let source_c = generate_source(
        from_file,
        &template.name,
        &constant_definitions,
        &size_computations,
        &input_size_checks,
        &output_size_checks,
        &cbor_instructions,
    );

    // TODO: finish the unittest
    let source_unittest = String::new();

    Ok(Codegen {
        source_h,
        source_c,
        source_unittest,
    })
}
