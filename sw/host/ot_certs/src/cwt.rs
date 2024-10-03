use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, Result, Context};
use heck::{ToShoutySnakeCase, ToUpperCamelCase};
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use crate::codegen::Codegen;

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CwtTemplate {
    /// Name of the certificate.
    pub name: String,
    /// Variable declarations.
    pub variables: IndexMap<String, VariableType>,
    /// Variable declarations.
    pub constants: IndexMap<String, ConstantType>,
    /// Certificate specification.
    pub certificate: StructureType,
}

/// Declaration of a variable that can be filled into the template.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum VariableType {
    /// Raw array of bytes.
    ByteArray {
        /// Length in bytes for this variable.
        size: usize,
    },
    /// Integer.
    Integer,
    /// UTF-8 encoded String.
    String {
        /// Maximum size in bytes for this variable.
        size: usize,
    },
}

impl VariableType {
    fn get_max_size(&self) -> usize {
        match self {
            VariableType::ByteArray{size} => 1 + 8 + size,
            VariableType::Integer => 1 + 8,
            VariableType::String{size} => 1 + 8 + size,
        }
    }
}

/// Declaration of a variable that can be filled into the template.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum ConstantType {
    /// Raw array of bytes.
    ByteArray {
        /// Big-endian hex-encoded bytes
        #[serde(with = "hex::serde")]
        value: Vec<u8>,
    },
    /// Integer.
    Integer {
        value: i64,
    },
    /// UTF-8 encoded String.
    String {
        value: String,
    },
}

impl ConstantType {
    fn get_max_size(&self) -> usize {
        match self {
            ConstantType::ByteArray{value} => 1 + 8 + value.len(),
            ConstantType::Integer{..} => 1 + 8,
            ConstantType::String{value} => 1 + 8 + value.len(),
        }
    }
}

/// Declaration of a variable that can be filled into the template.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(untagged)]
pub enum StructureType {
    Item(String),
    Map(IndexMap<String, StructureType>),
    Array(Vec<StructureType>),
}

impl StructureType {
    fn get_max_size(&self, variables: &IndexMap<String, VariableType>, constants: &IndexMap<String, ConstantType>) -> Result<usize> {
        let lookup = |var_name| {
            if let Some(var) = variables.get(var_name) {
                return Ok(var.get_max_size())
            }

            if let Some(var) = constants.get(var_name) {
                return Ok(var.get_max_size())
            }

            return Err(anyhow!("Cannot find {} in variables or constants", var_name));
        };

        match self {
            StructureType::Item(var_name) => lookup(var_name),
            StructureType::Map(map) => {
                let mut size: usize = 1 + 8;
                for (k, v) in map.iter() {
                    size += lookup(k)?;
                    size += v.get_max_size(variables, constants)?;
                }

                Ok(size)
            },
            StructureType::Array(arr) => {
                let mut size: usize = 1 + 8;
                for v in arr.iter() {
                    size += v.get_max_size(variables, constants)?;
                }

                Ok(size)
            },
        }
    }
}

pub fn load_cwt_template(path: &PathBuf) -> Result<CwtTemplate> {
    // Load template.
    let template_content = fs::read_to_string(path)
        .with_context(|| format!("Could not load the template file {}", path.display()))?;

    CwtTemplate::from_hjson_str(&template_content)
}

impl CwtTemplate {
    pub fn from_hjson_str(content: &str) -> Result<CwtTemplate> {
        Ok(deser_hjson::from_str(content)?)
    }
}

fn generate_c_var(template: &CwtTemplate, indent: &str) -> Result<String> {
    let mut vars = String::new();
    for (key, var) in template.variables.iter() {
        match var {
            VariableType::ByteArray{..} => {
                vars += &indoc::formatdoc! { r#"
                {indent}uint8_t *{key};
                {indent}size_t {key}_size;
                "#};
            },
            VariableType::Integer => {
                vars += &indoc::formatdoc! { r#"
                {indent}int32_t {key};
                "#};
            },
            VariableType::String{..} => {
                vars += &indoc::formatdoc! { r#"
                {indent}char *{key};
                {indent}size_t {key}_size;
                "#};
            },
        }
    }

    Ok(vars)
}

fn generate_header(from_file: &str, template: &CwtTemplate) -> Result<String> {
    let tmpl_name = &template.name;
    let preproc_guard_include = tmpl_name.to_shouty_snake_case();
    let enum_name = tmpl_name.to_upper_camel_case();
    let max_size = template.certificate.get_max_size(&template.variables, &template.constants)?;
    let vars = generate_c_var(template, "  ")?;

    let header_template = indoc::formatdoc! { r#"
    // Copyright lowRISC contributors (OpenTitan project).
    // Licensed under the Apache License, Version 2.0, see LICENSE for details.
    // SPDX-License-Identifier: Apache-2.0

    // This file was automatically generated using opentitantool from:
    // {from_file}
    #ifndef __{preproc_guard_include}__
    #define __{preproc_guard_include}__

    #include "sw/device/lib/base/status.h"

    typedef struct {tmpl_name}_tbs_values {{
    {vars}
    }} {tmpl_name}_tbs_values_t;

    enum {{
      k{enum_name}MaxTbsSizeBytes = {max_size},
    }};

    rom_error_t {tmpl_name}_build_tbs({tmpl_name}_tbs_values_t *values, uint8_t *tbs, size_t *tbs_inout_size);

    #endif
    "#};

    Ok(header_template)
}

fn generate_variable_code(name: &str, cur: &VariableType, indent: &str) -> Result<String> {
    match cur {
        VariableType::ByteArray{..} => {
            Ok(indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_write_bstr(&cbor, values->{name}, values->{name}_size));
            "#})
        },
        VariableType::Integer => {
            Ok(indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_write_int(&cbor, values->{name}));
            "#})
        },
        VariableType::String{..} => {
            Ok(indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_write_tstr(&cbor, values->{name}, values->{name}_size));
            "#})
        }
    }
}

fn generate_constant_definition(template: &CwtTemplate) -> Result<String> {
    let mut def = String::new();
    for (k, v) in template.constants.iter() {
        match v {
            ConstantType::ByteArray{value} => {
                let name = k.to_upper_camel_case();
                let val = value.iter().map(|ch| format!("0x{:02x}, ", ch)).collect::<String>();
                let len = value.len();
                def += &indoc::formatdoc! { r#"
                static const uint8_t k{name}[{len}] = {{{val}}};
                "#};
            },
            ConstantType::String{value} => {
                let name = k.to_upper_camel_case();
                let len = value.len();
                def += &indoc::formatdoc! { r#"
                static const char *k{name} = "{value}";
                "#};
            },
            _ => {},
        }
    }

    Ok(def)
}

fn generate_constant_code(name: &str, cur: &ConstantType, indent: &str) -> Result<String> {
    match cur {
        ConstantType::ByteArray{value} => {
            let name = format!("k{}", name.to_upper_camel_case());
            Ok(indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_write_bstr(&cbor, {name}, sizeof({name})));
            "#})
        },
        ConstantType::Integer{value} => {
            let val = value.to_string();
            Ok(indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_write_int(&cbor, {val}));
            "#})
        },
        ConstantType::String{value} => {
            let name = format!("k{}", name.to_upper_camel_case());
            Ok(indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_write_tstr(&cbor, {name}, sizeof({name}) - 1));
            "#})
        },
    }
}

fn generate_code(cur: &StructureType, template: &CwtTemplate, indent: &str) -> Result<String> {
    let mut code = String::new();
    let lookup = |var_name: &str, indent: &str| {
        if let Some(var) = template.variables.get(var_name) {
            return generate_variable_code(var_name, var, indent);
        }

        if let Some(var) = template.constants.get(var_name) {
            return generate_constant_code(var_name, var, indent);
        }

        return Err(anyhow!("Cannot find {} in variables or constants", var_name));
    };

    match cur {
        StructureType::Item(var_name) => {
            code += &lookup(var_name, indent)?;
        },
        StructureType::Map(map) => {
            let pair_count = map.len();
            let mut inner_code = String::new();
            let inner_indent = &(indent.to_owned() + indent);
            for (k, v) in map.iter() {
                inner_code += &lookup(k, inner_indent)?;
                inner_code += &generate_code(v, template, inner_indent)?;
            }

            code += &indoc::formatdoc! { r#"
            {indent}HARDENED_RETURN_IF_ERROR(cbor_map_init(&cbor, {pair_count}));
            {indent}{{
            {inner_code}
            {indent}}}
            "#};
        },
        StructureType::Array(arr) => unimplemented!(),
    }

    Ok(code)
}

fn generate_source(from_file: &str, template: &CwtTemplate) -> Result<String> {
    let tmpl_name = &template.name;
    let def = generate_constant_definition(template)?;
    let implement = generate_code(&template.certificate, template, "  ")?;

    let header_template = indoc::formatdoc! { r#"
    // Copyright lowRISC contributors (OpenTitan project).
    // Licensed under the Apache License, Version 2.0, see LICENSE for details.
    // SPDX-License-Identifier: Apache-2.0

    // This file was automatically generated using opentitantool from:
    // {from_file}

    #include "{tmpl_name}.h"
    #include "sw/device/silicon_creator/lib/cert/cbor.h"

    {def}

    rom_error_t {tmpl_name}_build_tbs({tmpl_name}_tbs_values_t *values, uint8_t *tbs, size_t *tbs_inout_size) {{
      struct CborOut cbor;
      HARDENED_RETURN_IF_ERROR(cbor_write_out_init(&cbor, tbs, *tbs_inout_size));

    {implement}

      *tbs_inout_size = CborOutSize(&cbor);
      return kErrorOk;
    }}
    "#};

    Ok(header_template)
}

pub fn generate_cert(template: &CwtTemplate) -> Result<Codegen> {
    let source_h = generate_header("test", template)?;
    let source_c = generate_source("test", template)?;
    let source_unittest = String::new();

    Ok(Codegen {
        source_h,
        source_c,
        source_unittest
    })
}
