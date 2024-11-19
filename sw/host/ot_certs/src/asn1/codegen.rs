// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use heck::{ToSnakeCase, ToUpperCamelCase};
use indexmap::IndexMap;
use num_bigint_dig::BigUint;

use crate::asn1::builder::Builder;
use crate::asn1::{Oid, Tag};
use crate::template::{Conversion, Value, Variable, VariableType};

struct ConstantEntry {
    var_name: String,
    c_decl: String,
}

/// Constant pool for code generation.
#[derive(Default)]
pub struct ConstantPool {
    constants: IndexMap<Vec<u8>, ConstantEntry>,
}

impl ConstantPool {
    pub fn new() -> ConstantPool {
        ConstantPool {
            constants: IndexMap::new(),
        }
    }

    pub fn codestring(&self) -> String {
        self.constants
            .values()
            .map(|x| x.c_decl.clone())
            .collect::<Vec<_>>()
            .join("")
    }

    pub fn get_var_name(&self, data: &Vec<u8>) -> Option<String> {
        self.constants.get(data).map(|ent| ent.var_name.clone())
    }

    pub fn add_entry(&mut self, data: Vec<u8>, var_name: String, c_decl: String) {
        self.constants
            .insert(data, ConstantEntry { var_name, c_decl });
    }
}

/// Information about how to refer to a variable in the code.
#[derive(Debug, Clone)]
pub enum VariableCodegenInfo {
    /// Variable can be referred to as a pointer.
    Pointer {
        // Expression generating the pointer.
        ptr_expr: String,
        // Expression generating the size.
        size_expr: String,
    },
    /// Variable is an integer.
    Int32 {
        // Expression generating the value.
        value_expr: String,
    },
    /// Variable is a boolean,
    Boolean {
        // Expression generating the value.
        value_expr: String,
    },
}

/// Information about a variable.
#[derive(Debug, Clone)]
pub struct VariableInfo {
    /// Type of the variable.
    pub var_type: VariableType,
    /// How to refer to the variable.
    pub codegen: VariableCodegenInfo,
}

/// ASN1 code generator.
pub struct Codegen<'a> {
    /// Output buffer.
    output: String,
    /// Constant pool.
    constants: &'a mut ConstantPool,
    /// Indentation string.
    indent: String,
    /// Current indentation level.
    indent_lvl: usize,
    /// Variable types: return information about a variable by name.
    variable_info: &'a dyn Fn(&str) -> Result<VariableInfo>,
    /// Index of next tag (to guarantee unique names).
    tag_idx: usize,
    /// Maximum size of the output.
    max_out_size: usize,
}

impl Codegen<'_> {
    /// Generate code that corresponds to an ASN1 document described by a closure acting on a Builder.
    /// Returns the generated code and the maximum possible size of the output.
    ///
    /// # Arguments
    ///
    /// * `buf_name` - Name of the variable holding the pointer to the output buffer.
    /// * `buf_size_name` - Name of the variable holding the size of the output buffer.
    ///   This variable is updated by the code to hold the actual size of the data after production.
    /// * `indent` - Identation string (one level).
    /// * `indent_lvl` - Initial identation level.
    /// * `constants` - Constant pool used to create necessary constants for the code.
    /// * `variables` - Description of the variable types used when producing the output.
    /// * `gen` - Closure generating the ASN1 document.
    pub fn generate(
        buf_name: &str,
        buf_size_name: &str,
        indent: &str,
        indent_lvl: usize,
        constants: &mut ConstantPool,
        variable_info: &dyn Fn(&str) -> Result<VariableInfo>,
        gen: impl FnOnce(&mut Codegen) -> Result<()>,
    ) -> Result<(String, usize)> {
        let mut builder = Codegen {
            output: String::new(),
            constants,
            indent: indent.to_string(),
            indent_lvl,
            variable_info,
            tag_idx: 0,
            max_out_size: 0,
        };
        // Create an ASN1 state, start with the provided buffer and carry on with
        // building the document with closure.
        builder.push_str_with_indent("asn1_state_t state;\n");
        builder.push_str_with_indent(&format!(
            "RETURN_IF_ERROR(asn1_start(&state, {buf_name}, *{buf_size_name}));\n"
        ));
        gen(&mut builder)?;
        // Finish the document and update the size variable.
        builder.push_str_with_indent(&format!(
            "RETURN_IF_ERROR(asn1_finish(&state, {buf_size_name}));\n"
        ));
        Ok((builder.output, builder.max_out_size))
    }

    /// Push indentation into the output buffer.
    fn push_indent(&mut self) {
        let indent = self.indent.to_string();
        for _ in 0..self.indent_lvl {
            self.push_str(&indent);
        }
    }

    /// Push raw string into the output buffer.
    fn push_str(&mut self, s: &str) {
        self.output.push_str(s);
    }

    /// Push raw string with indentation into the output buffer.
    fn push_str_with_indent(&mut self, s: &str) {
        self.push_indent();
        self.push_str(s);
    }

    /// Register a constant byte array.
    fn add_constant_byte_array(&mut self, name_hint: Option<String>, data: &[u8]) -> String {
        // If constant already exist, do not recreate it
        if let Some(name) = self.constants.get_var_name(&data.to_vec()) {
            return name;
        }

        let const_name = format!(
            "kConstant{}",
            name_hint
                .map(|x| x.to_upper_camel_case())
                .unwrap_or("".into())
        );
        let bytes = data
            .iter()
            .map(|b| format!("{:#04x}", b))
            .collect::<Vec<_>>()
            .join(", ");
        self.constants.add_entry(
            data.to_vec(),
            const_name.clone(),
            format!("static const uint8_t {const_name}[] = {{ {} }};\n", bytes),
        );
        const_name
    }

    /// Return the maximum size of ASN1 tag, ie the tag itself, the length.
    fn tag_size(max_size: usize) -> usize {
        // For now, assume that all tags fit on one byte since that's the only
        // option supported by the asn1 library anyway.
        let tag_bytes = 1;
        // The asn1 library only supports tag with up to 0xffff bytes of data
        // so use this as an upper bound.
        let len_bytes = if max_size <= 0x7f {
            // The length fits on a single byte.
            1
        } else if max_size <= 0xff {
            // The length requires one byte to specify the number of bytes
            // and just one byte to hold the value.
            2
        } else if max_size <= 0xffff {
            // The length requires one byte to specify the number of bytes
            // and two bytes to hold the value.
            3
        } else {
            panic!("the asn1 library only supports tag with length up to 0xffff");
        };
        tag_bytes + len_bytes
    }

    // Same as `tag_size` but also count the content size.
    fn tag_and_content_size(size: usize) -> usize {
        Self::tag_size(size) + size
    }

    /// Push a tagged raw OID into the ASN1 output, the buffer and its size are arbitrary C expressions.
    fn push_raw_oid(&mut self, expr: &str, expr_size: &str, max_size: usize) {
        // A tagged OID needs a tag, up to 3 bytes of length and the OID itself.
        // Don't try to exactly compute how many bytes we need for the length.
        self.max_out_size += Self::tag_and_content_size(max_size);
        self.push_str_with_indent(&format!(
            "asn1_push_oid_raw(&state, {expr}, {expr_size});\n"
        ))
    }

    /// Push a bit in a bitstring.
    fn push_bit(&mut self, bitstring_tagname: &str, val: &Value<bool>) -> Result<()> {
        match val {
            Value::Literal(x) => {
                self.push_str_with_indent(&format!(
                    "asn1_bitstring_push_bit({bitstring_tagname}, {x});\n"
                ));
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                match source_type {
                    VariableType::Boolean => {
                        ensure!(
                            convert.is_none(),
                            "cannot use a convertion from boolean to boolean"
                        );
                        let VariableCodegenInfo::Boolean { value_expr } = codegen else {
                            bail!("internal error: boolean not represented by a VariableCodegenInfo::Boolean");
                        };
                        self.push_str_with_indent(&format!(
                            "asn1_bitstring_push_bit({bitstring_tagname}, {value_expr});\n"
                        ));
                    }
                    _ => bail!(
                        "conversion from to {:?} to boolean is not supported",
                        source_type
                    ),
                }
            }
        }
        Ok(())
    }
}

impl Tag {
    // Return the value that corresponds to a tag and can be passed to asn1 functions.
    fn codestring(&self) -> String {
        match self {
            Tag::Oid => "kAsn1TagNumberOid".into(),
            Tag::Boolean => "kAsn1TagNumberBoolean".into(),
            Tag::Integer => "kAsn1TagNumberInteger".into(),
            Tag::GeneralizedTime => "kAsn1TagNumberGeneralizedTime".into(),
            Tag::PrintableString => "kAsn1TagNumberPrintableString".into(),
            Tag::Utf8String => "kAsn1TagNumberUtf8String".into(),
            Tag::Sequence => "kAsn1TagNumberSequence".into(),
            Tag::Set => "kAsn1TagNumberSet".into(),
            Tag::OctetString => "kAsn1TagNumberOctetString".into(),
            Tag::BitString => "kAsn1TagNumberBitString".into(),
            &Tag::Context { constructed, value } => format!(
                "kAsn1TagClassContext{} | {value}",
                if constructed {
                    " | kAsn1TagFormConstructed"
                } else {
                    ""
                }
            ),
        }
    }
}

impl Builder for Codegen<'_> {
    /// Push a byte into the ASN1 output, the value can be any C expression.
    fn push_byte(&mut self, val: u8) -> Result<()> {
        self.push_str_with_indent(&format!("asn1_push_byte(&state, {val});\n"));
        self.max_out_size += 1;
        Ok(())
    }

    /// Push a tagged boolean into the ASN1 output.
    fn push_boolean(&mut self, tag: &Tag, val: &Value<bool>) -> Result<()> {
        match val {
            Value::Literal(x) => {
                let bool_str = if *x { "true" } else { "false" };
                self.push_str_with_indent(&format!(
                    "asn1_push_bool(&state, {}, {});\n",
                    tag.codestring(),
                    bool_str
                ));
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                // Verify that type is correct.
                match source_type {
                    VariableType::Boolean =>
                        ensure!(convert.is_none(), "using an boolean variable for an boolean field cannot specify a conversion"),
                    _ => bail!(
                        "using a variable of type {source_type:?} for a boolean field is not supported"
                        ),
                }
                match codegen {
                    VariableCodegenInfo::Boolean { value_expr } => {
                        self.push_str_with_indent(&format!(
                            "asn1_push_bool(&state, {}, {value_expr});\n",
                            tag.codestring()
                        ))
                    }
                    _ => bail!("internal error: boolean represented by a {source_type:?}"),
                }
            }
        }
        // A boolean only requires one byte of data (plus the tag).
        self.max_out_size += Self::tag_and_content_size(1);
        Ok(())
    }

    /// Push a tagged integer into the ASN1 output, the buffer (a big-endian integer) and its size
    /// are arbitrary C expressions.
    fn push_integer(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        val: &Value<BigUint>,
    ) -> Result<()> {
        match val {
            // For a literal, try to use `asn1_push_uint32` if possible, otherwise
            // create a constant in the pool to hold the encoding and use `asn1_push_integer`.
            // For unsigned integers, we might need to push one more byte of data then indicated
            // by the length since they are represented in two's completement so an unsigned number
            // with the MSB bit set needs to be padded with a 0x00 byte so that it is not interpreted
            // as a negative number. Therefore, always add one to estimate.
            Value::Literal(x) => {
                if x.bits() <= 32 {
                    self.push_str_with_indent(&format!(
                        "asn1_push_uint32(&state, {}, {x});\n",
                        tag.codestring()
                    ));
                    self.max_out_size += Self::tag_and_content_size(1 + (x.bits() + 7) / 8);
                } else {
                    let bytes = x.to_bytes_be();
                    let const_name = self.add_constant_byte_array(name_hint, &bytes);
                    self.push_str_with_indent(
                        &format!(
                            "asn1_push_integer(&state, {}, false, {const_name}, sizeof({const_name}));\n",
                            tag.codestring())
                    );
                    self.max_out_size += Self::tag_and_content_size(1 + bytes.len())
                }
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                // Get the maximum size and verify that types and conversion are correct.
                let size = match source_type {
                    VariableType::Integer { size } => {
                        ensure!(convert.is_none(), "using an integer variable for an integer field cannot specify a conversion");
                        size
                    }
                    VariableType::ByteArray { size } => {
                        match convert {
                            None => bail!("using a byte array variable for an integer field must specify a conversion"),
                            Some(Conversion::BigEndian) => (),
                            _ => bail!("conversion {:?} from byte array to integer is not supported", convert),
                        }
                        size
                    }
                    _ => bail!(
                        "using a variable of type {source_type:?} for an integer field is not supported"
                        ),
                };
                self.max_out_size += Self::tag_and_content_size(1 + size);
                // For variables, an integer can either be represented by a pointer to a big-endian
                // byte array, or by a `uint32_t` for a very small integers. Use `asn1_push_uint32`
                // or `asn1_push_integer` depending on the case.
                match codegen {
                    VariableCodegenInfo::Int32 { value_expr } => {
                        self.push_str_with_indent(&format!(
                            "asn1_push_uint32(&state, {}, {value_expr});\n",
                            tag.codestring()
                        ))
                    }
                    VariableCodegenInfo::Pointer {
                        ptr_expr,
                        size_expr,
                    } => {
                        // Make sure the type is correct and get the size.
                        self.push_str_with_indent(&format!(
                            "asn1_push_integer(&state, {}, false, {ptr_expr}, {size_expr});\n",
                            tag.codestring()
                        ))
                    }
                    _ => bail!("internal error: integer represented by a {source_type:?}"),
                }
            }
        }
        Ok(())
    }

    /// Push a byte array into the ASN1 output, represeting an integer. If the provided buffer is too small,
    /// it will be padded with zeroes. Note that this function does not add a tag to the ASN1 output.
    fn push_integer_pad(
        &mut self,
        name_hint: Option<String>,
        val: &Value<BigUint>,
        size: usize,
    ) -> Result<()> {
        match val {
            Value::Literal(x) => {
                let data = &x.to_bytes_be();
                let data = [vec![0; size - data.len()], data.clone()].concat();
                let const_name = self.add_constant_byte_array(name_hint, &data);
                self.push_str_with_indent(&format!(
                    "asn1_push_bytes(&state, {const_name}, sizeof({const_name}));\n"
                ));
                // There is not tag, we are just pushing the data itself.
                self.max_out_size += data.len();
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                match source_type {
                    VariableType::Integer { size } => {
                        ensure!(convert.is_none(), "using an integer variable for an integer field cannot specify a conversion");
                        let VariableCodegenInfo::Pointer {
                            ptr_expr,
                            size_expr,
                        } = codegen
                        else {
                            bail!("the codegen backend does not support small integers for padded integer fields");
                        };
                        // There is not tag, we are just pushing the data itself.
                        self.max_out_size += size;
                        self.push_str_with_indent(&format!(
                            "asn1_push_integer_pad(&state, false, {ptr_expr}, {size_expr}, {size});\n"
                        ))
                    }
                    _ => bail!(
                        "using a variable of type {source_type:?} for a padded integer field is not supported"
                    ),
                }
            }
        }
        Ok(())
    }

    /// Push a byte array of fixed length into the ASN1 output. Note that this function does not add a tag to
    /// the ASN1 output.
    fn push_byte_array(&mut self, name_hint: Option<String>, val: &Value<Vec<u8>>) -> Result<()> {
        match val {
            Value::Literal(x) => {
                let const_name = self.add_constant_byte_array(name_hint, x);
                self.push_str_with_indent(&format!(
                    "asn1_push_bytes(&state, {const_name}, sizeof({const_name}));\n"
                ));
                // There is not tag, we are just pushing the data itself.
                self.max_out_size += x.len();
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                match source_type {
                    VariableType::ByteArray { size } => {
                        ensure!(convert.is_none(), "using a byte-array variable for a byte-array field cannot specify a conversion");
                        let VariableCodegenInfo::Pointer {
                            ptr_expr,
                            size_expr,
                        } = codegen
                        else {
                            bail!("internal error: byte-array represented by a VariableCodegenInfo::Int32");
                        };
                        // There is not tag, we are just pushing the data itself.
                        self.max_out_size += size;
                        self.push_str_with_indent(&format!(
                            "asn1_push_bytes(&state, {ptr_expr}, {size_expr});\n"
                        ))
                    }
                    _ => bail!(
                        "using a variable of type {source_type:?} for a byte-array field is not supported",
                    ),
                }
            }
        }
        Ok(())
    }

    /// Push an optionally tagged string into the ASN1 output.
    fn push_string(
        &mut self,
        _name_hint: Option<String>,
        str_type: &Tag,
        val: &Value<String>,
    ) -> Result<()> {
        let str_type = str_type.codestring();
        match val {
            Value::Literal(x) => {
                let len = x.len();
                self.push_str_with_indent(&format!(
                    "asn1_push_string(&state, {str_type}, \"{x}\", {len});\n"
                ));
                // A tagged string needs a tag (up to 3 bytes of length) and the string itself.
                // Don't try to exactly compute how many bytes we need for the length.
                self.max_out_size += Self::tag_and_content_size(x.len());
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                // When pushing a variable, it can either a string (use asn1_push_string) or a byte array
                // that needs to converted (use asn1_push_hexstring).
                match source_type {
                    VariableType::String { size } => {
                        ensure!(
                            convert.is_none(),
                            "cannot use a convertion from string to string"
                        );
                        let VariableCodegenInfo::Pointer {
                            ptr_expr,
                            size_expr,
                        } = codegen
                        else {
                            bail!("internal error: string not represented by a VariableCodegenInfo::Pointer");
                        };
                        self.push_str_with_indent(&format!(
                            "asn1_push_string(&state, {str_type}, {ptr_expr}, {size_expr});\n"
                        ));
                        self.max_out_size += Self::tag_and_content_size(size);
                    }
                    VariableType::ByteArray { size } => {
                        match convert {
                            None => bail!("using a byte array variable for an string field must to specify a conversion"),
                            Some(Conversion::LowercaseHex) => {
                                let VariableCodegenInfo::Pointer { ptr_expr, size_expr } = codegen else {
                                    bail!("internal error: string not represented by a VariableCodegenInfo::Pointer");
                                };
                                // The conversion doubles the size.
                                self.max_out_size += Self::tag_and_content_size(2 * size);
                                self.push_str_with_indent(
                                    &format!("asn1_push_hexstring(&state, {str_type}, {ptr_expr}, {size_expr});\n"))
                            }
                            _ => bail!("conversion {convert:?} from byte array to string is not supported"),
                        }
                    }
                    _ => bail!("conversion from to {source_type:?} to string is not supported",),
                }
            }
        }
        Ok(())
    }

    fn push_bitstring<'a>(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        bits: &[Value<bool>],
    ) -> Result<()> {
        self.push_tag(name_hint.clone(), tag, |builder| {
            let tag_name = format!(
                "bit{}_{}",
                builder.tag_idx,
                name_hint.map(|x| x.to_snake_case()).unwrap_or("".into())
            );
            builder.tag_idx += 1;
            builder.push_str_with_indent(&format!("asn1_bitstring_t {tag_name};\n"));
            builder.push_str_with_indent(&format!("asn1_start_bitstring(&state, &{tag_name});\n"));
            builder.push_str_with_indent("{\n");
            builder.indent_lvl += 1;
            for bit in bits {
                builder.push_bit(&format!("&{tag_name}"), bit)?;
            }
            // One byte for the unused bits and then one byte per 8 bits.
            builder.max_out_size += 1 + (bits.len() + 7) / 8;
            builder.indent_lvl -= 1;
            builder.push_str_with_indent("}\n");
            builder.push_str_with_indent(&format!("asn1_finish_bitstring(&{tag_name});\n"));
            Ok(())
        })
    }

    fn push_oid(&mut self, oid: &Oid) -> Result<()> {
        // Create constant.
        let bytes = oid.to_der()?;
        let oid_const_name = self.add_constant_byte_array(Some(format!("oid_{}", oid)), &bytes);
        self.push_raw_oid(
            &oid_const_name,
            &format!("sizeof({oid_const_name})"),
            bytes.len(),
        );

        Ok(())
    }

    // Helper function for outputting ASN1 tags.
    fn push_tag(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        gen: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        let tag_name = format!(
            "tag{}_{}",
            self.tag_idx,
            name_hint.map(|x| x.to_snake_case()).unwrap_or("".into())
        );
        self.tag_idx += 1;
        self.push_str_with_indent(&format!("asn1_tag_t {tag_name};\n"));
        self.push_str_with_indent(&format!(
            "asn1_start_tag(&state, &{tag_name}, {});\n",
            tag.codestring()
        ));
        self.push_str_with_indent("{\n");
        self.indent_lvl += 1;
        // We do not yet know how many bytes the content will use: remember the current
        // value of the estimate and see by how much it increases during generation
        // to obtain a bound.
        let old_max_size = self.max_out_size;
        gen(self)?;
        let max_size = self.max_out_size - old_max_size;
        self.max_out_size += Self::tag_size(max_size);
        self.indent_lvl -= 1;
        self.push_str_with_indent("}\n");
        self.push_str_with_indent(&format!("asn1_finish_tag(&{tag_name});\n"));
        Ok(())
    }
}
