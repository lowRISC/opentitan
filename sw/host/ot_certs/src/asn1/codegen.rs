// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use itertools::Itertools;
use num_bigint_dig::BigUint;
use std::cmp::max;

use crate::asn1::builder::Builder;
use crate::asn1::der::Der;
use crate::asn1::{Oid, Tag};
use crate::template::{Conversion, Value, Variable, VariableType};

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
    Uint32 {
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

// Each CodegenStructure maps to a CodeOutput.
type CodeOutput = Vec<CodeChunkWithComment>;

#[derive(Debug, Clone)]
struct CodeChunkWithComment {
    code: CodeChunk,
    comment: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CodeChunk {
    // A code snippet.
    Code(String),
    // If all the arguments are constants, derive its resulting bytes directly.
    ConstBytes(Vec<u8>),
    // Patch the last two bytes with length delta.
    SizePatchMemo(i16),
    // Create a new nested block with left curly brace.
    OpenBlock,
    // Close a nested block. It should be paired with OpenBlock.
    CloseBlock,
}

impl CodeChunk {
    fn is_constant(&self) -> bool {
        match self {
            CodeChunk::Code(_) => false,
            CodeChunk::ConstBytes(_) => true,
            CodeChunk::SizePatchMemo(_) => true,
            CodeChunk::OpenBlock => true,
            CodeChunk::CloseBlock => true,
        }
    }
    fn len(&self) -> usize {
        match self {
            CodeChunk::Code(_) => panic!("Variable has no size"),
            CodeChunk::ConstBytes(x) => x.len(),
            _ => 0,
        }
    }
}

/// ASN1 code generator.
pub struct Codegen<'a> {
    /// Output buffer.
    output: CodeOutput,
    /// Variable types: return information about a variable by name.
    variable_info: &'a dyn Fn(&str) -> Result<VariableInfo>,
    /// Minimum size of the output.
    min_out_size: usize,
    /// Maximum size of the output.
    max_out_size: usize,
}

/// ASN1 code generator output.
pub struct CodegenOutput {
    /// Output code.
    pub code: String,
    /// Minimum size of the produced cert/TBS.
    pub min_size: usize,
    /// Maximum size of the produced cert/TBS.
    pub max_size: usize,
}

impl Codegen<'_> {
    /// Generate code that corresponds to an ASN1 document described by a closure acting on a Builder.
    /// Returns the generated code and the min/max possible size of the output.
    ///
    /// # Arguments
    ///
    /// * `buf_name` - Name of the variable holding the pointer to the output buffer.
    /// * `buf_size_name` - Name of the variable holding the size of the output buffer.
    ///   This variable is updated by the code to hold the actual size of the data after production.
    /// * `variables` - Description of the variable types used when producing the output.
    /// * `build` - Closure generating the ASN1 document.
    pub fn generate(
        buf_name: &str,
        buf_size_name: &str,
        variable_info: &dyn Fn(&str) -> Result<VariableInfo>,
        build: impl FnOnce(&mut Codegen) -> Result<()>,
    ) -> Result<CodegenOutput> {
        let mut builder = Codegen {
            output: CodeOutput::new(),
            variable_info,
            min_out_size: 0,
            max_out_size: 0,
        };
        build(&mut builder)?;

        let mut output = String::new();
        let mut const_bytes = Vec::<u8>::new();
        let mut size_patches = Vec::<(usize, i16)>::new();

        // For neighboring const chunks, we collect them into a single array and write them at once.
        for (is_code, chunk) in &builder
            .output
            .iter()
            .chunk_by(|inst| !inst.code.is_constant())
        {
            if !is_code {
                let mut nbytes = 0;

                for CodeChunkWithComment { code, comment } in chunk {
                    nbytes += &code.len();
                    match &code {
                        CodeChunk::OpenBlock => output.push_str("{\n"),
                        CodeChunk::CloseBlock => output.push_str("};\n"),
                        CodeChunk::SizePatchMemo(delta) => {
                            size_patches.push((const_bytes.len(), *delta));

                            // The bytes in (nbytes-2..nbytes) will be patched.
                            let patch_offset = nbytes - 2;
                            output.push_str(&format!(
                                "
                                    /* Size patch with delta {delta} */
                                    template_pos_t memo = template_save_pos(&state, {patch_offset});
                                "
                            ));
                        }
                        CodeChunk::ConstBytes(data) => {
                            // Add comment about the const in-place.
                            if let Some(comment) = &comment {
                                output.push_str(&format!("/* {comment} */\n"));
                            }

                            // But collect the actual bytes to the shared pool.
                            if !data.is_empty() {
                                const_bytes.extend(data);
                                let data = data.iter().map(|ch| format!("0x{:02x}", ch)).join(", ");
                                output.push_str(&format!("/*   {data} */\n"));
                            }
                        }
                        _ => unreachable!(),
                    }
                }

                // Output the combined const segment.
                if nbytes > 0 {
                    output.push_str(&format!(
                        "template_push_const(&state, /*nbytes=*/{nbytes});\n"
                    ));
                }
            } else {
                /* is_code == true */
                for CodeChunkWithComment { code, comment } in chunk {
                    if let Some(comment) = comment {
                        output.push_str(&format!("/* {comment} */\n"));
                    }
                    match &code {
                        CodeChunk::Code(inner) => output.push_str(inner),
                        _ => unreachable!(),
                    }
                }
            }
        }

        // Apply the size delta to the pregenerated const bytes in the reversed order.
        for (idx, value) in size_patches.iter().rev() {
            let patch_point = &mut const_bytes[idx - 2..*idx];
            let old_value = u16::from_be_bytes(patch_point.try_into().unwrap());
            let new_value = old_value.wrapping_add_signed(*value);
            patch_point.copy_from_slice(&new_value.to_be_bytes());
        }

        let const_bytes = const_bytes
            .iter()
            .map(|ch| format!("0x{:02x}", ch))
            .join(", ");
        let max_size = builder.max_out_size;
        output = format!(
            "
                if (*{buf_size_name} < {max_size}) {{
                    return kErrorCertInvalidSize;
                }}

                const static uint8_t kTemplateConstBytes[] = {{{const_bytes}}};
                template_state_t state;

                template_init(&state, {buf_name}, kTemplateConstBytes);

                {output}

                *{buf_size_name} = template_finalize(&state);
            "
        );

        Ok(CodegenOutput {
            code: output,
            min_size: builder.min_out_size,
            max_size: builder.max_out_size,
        })
    }

    /// Push a chunk to the output stream.
    fn push_chunk(&mut self, code: CodeChunk, comment: Option<String>) {
        self.output.push(CodeChunkWithComment { code, comment });
    }

    /// Start a new nested block in the output stream.
    /// It should be paired with an `unindent()` call.
    fn indent(&mut self) {
        self.push_chunk(CodeChunk::OpenBlock, None);
    }

    /// Close one level of nested block.
    /// It should be paired with an `indent()` call.
    fn unindent(&mut self) {
        self.push_chunk(CodeChunk::CloseBlock, None);
    }

    /// Push raw const bytes into the output stream.
    fn push_const(&mut self, comment: Option<String>, value: &[u8]) {
        self.min_out_size += value.len();
        self.max_out_size += value.len();
        self.push_chunk(CodeChunk::ConstBytes(value.to_owned()), comment);
    }

    /// Push a constified DER built by the `build` function.
    fn push_der(
        &mut self,
        comment: Option<String>,
        build: impl FnOnce(&mut Der) -> Result<()>,
    ) -> Result<()> {
        let content = Der::generate(build)?;
        self.push_const(comment, &content);
        Ok(())
    }

    /// Push raw code with size difference into the output stream.
    fn push_function_call(&mut self, min_size: usize, max_size: usize, s: &str) {
        self.min_out_size += min_size;
        self.max_out_size += max_size;
        self.push_chunk(CodeChunk::Code(s.to_owned()), None);
    }

    /// Get the placeholder for length octet encoded with DER.
    fn get_size_placeholder(min_size: usize, max_size: usize) -> Result<Vec<u8>> {
        // DER requires the length octet encoded in minimum bytes.
        let tag_size = Self::tag_size(max_size);
        ensure!(
            Self::tag_size(min_size) == tag_size,
            "Var-sized length octet is not supported,\
             max={max_size},\
             min={min_size}"
        );

        let mut len_enc = Vec::<u8>::new();
        if max_size <= 0x7f {
            len_enc.push(0);
        } else {
            let nbytes = Self::tag_size(max_size) - 2;
            len_enc.push(0x80 | (nbytes as u8));
            len_enc.extend(std::iter::repeat(0).take(nbytes));
        }

        Ok(len_enc)
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
        self.push_const(Some("Byte".into()), &[val]);
        Ok(())
    }

    /// Push a tagged boolean into the ASN1 output.
    fn push_boolean(&mut self, tag: &Tag, val: &Value<bool>) -> Result<()> {
        match val {
            Value::Literal(_) => {
                self.push_der(Some(tag.codestring()), |builder| {
                    builder.push_boolean(tag, val)
                })?;
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
                        self.push_tag(Some(tag.codestring()), tag, |builder| {
                            // A boolean only requires one byte of data (plus the tag).
                            builder.push_function_call(
                                1,
                                1,
                                &format!("template_push_asn1_bool(&state, {value_expr});\n",),
                            );
                            Ok(())
                        })?;
                    }
                    _ => bail!("internal error: boolean represented by a {source_type:?}"),
                }
            }
        }
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
            Value::Literal(_) => {
                self.push_der(name_hint.clone(), |builder| {
                    builder.push_integer(name_hint, tag, val)
                })?;
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                // Get the maximum size and verify that types and conversion are correct.
                match source_type {
                    VariableType::Integer { .. } => {
                        ensure!(convert.is_none(), "using an integer variable for an integer field cannot specify a conversion");
                    },
                    VariableType::ByteArray { .. } => {
                        match convert {
                            None => bail!("using a byte array variable for an integer field must specify a conversion"),
                            Some(Conversion::BigEndian) => (),
                            _ => bail!("conversion {:?} from byte array to integer is not supported", convert),
                        }
                    },
                    _ => bail!(
                        "using a variable of type {source_type:?} for an integer field is not supported"
                        ),
                };

                // ASN1 integer will add one extra byte when positive integers
                // have MSB = 1.
                let (min_size, max_size) = source_type.int_size(1);

                // Value zero will be encoded as one-byte 0x00.
                let min_size = max(1, min_size);

                ensure!(
                    max_size < 126,
                    "Integer more than 126 bytes is not supported."
                );

                // Two extra bytes for tag and length.
                let (min_size, max_size) = (min_size + 2, max_size + 2);

                // For variables, an integer can either be represented by a pointer to a big-endian
                // byte array, or by a `uint32_t` for a very small integers. Use `template_push_uint32`
                // or `template_push_integer` depending on the case.
                let msb_tweak = source_type.use_msb_tweak();
                ensure!(
                    !msb_tweak || source_type.has_constant_array_size(),
                    "MSb tweak is only supported with constant array size.",
                );

                let tag_str = tag.codestring();
                match codegen {
                    VariableCodegenInfo::Uint32 { value_expr } => self.push_function_call(
                        min_size,
                        max_size,
                        &format!(
                            "template_asn1_uint32(&state, {tag_str}, {msb_tweak}, {value_expr});\n",
                        ),
                    ),
                    VariableCodegenInfo::Pointer {
                        ptr_expr,
                        size_expr,
                    } => {
                        // Make sure the type is correct and get the size.
                        self.push_function_call(
                            min_size,
                            max_size,
                            &format!(
                                "template_asn1_integer(&state, {tag_str}, {msb_tweak}, {ptr_expr}, {size_expr});\n",
                            ),
                        )
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
            Value::Literal(_) => {
                self.push_der(name_hint.clone(), |builder| {
                    builder.push_integer_pad(name_hint, val, size)
                })?;
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                match source_type {
                    VariableType::Integer { .. } => {
                        ensure!(convert.is_none(), "using an integer variable for an integer field cannot specify a conversion");
                        let VariableCodegenInfo::Pointer {
                            ptr_expr,
                            size_expr,
                        } = codegen
                        else {
                            bail!("the codegen backend does not support small integers for padded integer fields");
                        };

                        let (min_size, max_size) = source_type.array_size();
                        ensure!(min_size == max_size, "Padding is not supported");

                        // There is not tag, we are just pushing the data itself.
                        self.push_function_call(min_size, max_size, &format!(
                            "template_push_bytes(&state, {ptr_expr}, {size_expr});\n"
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
            Value::Literal(_) => {
                self.push_der(name_hint.clone(), |builder| {
                    builder.push_byte_array(name_hint, val)
                })?;
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                match source_type {
                    VariableType::ByteArray { .. } => {
                        ensure!(convert.is_none(), "using a byte-array variable for a byte-array field cannot specify a conversion");
                        let (min_size, max_size) = source_type.array_size();
                        let VariableCodegenInfo::Pointer {
                            ptr_expr,
                            size_expr,
                        } = codegen
                        else {
                            bail!("internal error: byte-array represented by a VariableCodegenInfo::Uint32");
                        };
                        // There is not tag, we are just pushing the data itself.
                        self.push_function_call(min_size, max_size, &format!(
                            "template_push_bytes(&state, {ptr_expr}, {size_expr});\n"
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
        name_hint: Option<String>,
        str_type: &Tag,
        val: &Value<String>,
    ) -> Result<()> {
        match val {
            Value::Literal(_) => {
                self.push_der(name_hint.clone(), |builder| {
                    builder.push_string(name_hint, str_type, val)
                })?;
            }
            Value::Variable(Variable { name, convert }) => {
                let VariableInfo {
                    codegen,
                    var_type: source_type,
                } = (self.variable_info)(name)?;
                // When pushing a variable, it can either a string (use template_push_bytes) or a byte array
                // that needs to converted (use template_push_hex).
                match source_type {
                    VariableType::String { .. } => {
                        ensure!(
                            convert.is_none(),
                            "cannot use a convertion from string to string"
                        );
                        let (min_size, max_size) = source_type.array_size();
                        let VariableCodegenInfo::Pointer {
                            ptr_expr,
                            size_expr,
                        } = codegen
                        else {
                            bail!("internal error: string not represented by a VariableCodegenInfo::Pointer");
                        };
                        self.push_tag(Some(name.into()), str_type, |builder| {
                            builder.push_function_call(
                                min_size,
                                max_size,
                                &format!("template_push_bytes(&state, (const uint8_t*){ptr_expr}, {size_expr});\n"),
                            );
                            Ok(())
                        })?;
                    }
                    VariableType::ByteArray { .. } => {
                        let (min_size, max_size) = source_type.array_size();
                        match convert {
                            None => bail!("using a byte array variable for an string field must to specify a conversion"),
                            Some(Conversion::LowercaseHex) => {
                                let VariableCodegenInfo::Pointer { ptr_expr, size_expr } = codegen else {
                                    bail!("internal error: string not represented by a VariableCodegenInfo::Pointer");
                                };
                                // The conversion doubles the size.
                                self.push_tag(Some(name.into()), str_type, |builder| {
                                    builder.push_function_call(2 * min_size, 2 * max_size, &format!(
                                        "template_push_hex(&state, {ptr_expr}, {size_expr});\n"
                                    ));
                                    Ok(())
                                })?;
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
        let bit_consts = bits
            .iter()
            .map(|x| match x {
                Value::Literal(x) => x,
                _ => &false,
            })
            .collect::<Vec<_>>();
        // See X.690 spec section 8.6 for encoding details.
        // Note: the encoding of an empty bitstring must be the number of unused bits to 0 and have no content.
        let nr_bytes = (bit_consts.len() + 7) / 8;
        let mut bytes = vec![0u8; nr_bytes];
        for (i, bit) in bit_consts.iter().enumerate() {
            bytes[i / 8] |= (**bit as u8) << (7 - (i % 8));
        }

        let bitstring_name = format!("{}-bit BitString {}", bits.len(), tag.codestring(),);

        self.push_as_bit_string(
            Some(bitstring_name),
            tag,
            bytes.len() * 8 - bits.len(),
            |builder| builder.push_byte_array(name_hint.clone(), &Value::Literal(bytes.clone())),
        )?;

        for (i, bit) in bits.iter().enumerate() {
            let byte_offset = bytes.len() - i / 8;
            let bit_offset = 7 - (i % 8);

            if let Value::Variable(Variable { name, convert }) = bit {
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
                        self.push_chunk(
                            CodeChunk::Code(format!(
                                "template_set_bit(&state, {byte_offset}, {bit_offset}, {value_expr});\n"
                            )),
                            Some(name.clone()),
                        );
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

    fn push_oid(&mut self, oid: &Oid) -> Result<()> {
        // Serialize oid with tag to const.
        self.push_der(Some(format!("Oid of {}", oid)), |builder| {
            builder.push_oid(oid)
        })
    }

    // Helper function for outputting ASN1 tags.
    fn push_tag(
        &mut self,
        name_hint: Option<String>,
        tag: &Tag,
        build: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        let tag_name = name_hint.unwrap_or("Unnamed tag".into());

        self.indent();

        self.push_const(
            Some(format!("Tag {} of {tag_name}", tag.codestring())),
            &tag.to_der()?,
        );

        // Allocate placeholders in the output stream.
        // This placeholder will be replaced by the encoded length later.
        let len_idx = self.output.len();
        self.push_const(None, &[]);
        // This placeholder will be replaced by the location memo code later.
        let memo_idx = self.output.len();
        self.push_const(None, &[]);

        let content_idx = self.output.len();

        // We do not yet know how many bytes the content will use: remember the current
        // value of the estimate and see by how much it increases during generation
        // to obtain a bound.
        let old_min_size = self.min_out_size;
        let old_max_size = self.max_out_size;
        self.indent();
        build(self)?;
        self.unindent();
        let min_size: usize = self.min_out_size - old_min_size;
        let max_size: usize = self.max_out_size - old_max_size;

        // Generate size patching code.
        let len_enc = Self::get_size_placeholder(min_size, max_size)?;
        self.min_out_size += len_enc.len();
        self.max_out_size += len_enc.len();

        if min_size == max_size {
            self.output[len_idx].comment = Some(format!("Length of fixed-sized {tag_name}"));

            // Sanity check for all constants.
            if self.output[content_idx..]
                .iter()
                .all(|x| x.code.is_constant())
            {
                let total_size: usize = self.output[content_idx..]
                    .iter()
                    .map(|x| x.code.len())
                    .sum();
                if total_size != min_size || total_size != max_size {
                    println!("{:?}", &self.output[content_idx..]);
                    panic!(
                        "Invalid const size total={total_size}, \
                         min={min_size}, M={max_size}"
                    );
                }
            }

            let len_enc = Der::encode_size(max_size);
            self.output[len_idx].code = CodeChunk::ConstBytes(len_enc);
            // The memo placeholder is left empty / no-op in this branch.
        } else {
            /* var-sized tag */
            self.output[len_idx].comment = Some(format!(
                "Length of {tag_name} between {min_size} ~ {max_size}"
            ));

            self.output[len_idx].code = CodeChunk::ConstBytes(len_enc);

            // Add the memo statement.
            self.output[memo_idx] = CodeChunkWithComment {
                code: CodeChunk::SizePatchMemo(-2),
                comment: Some(format!("Start of {tag_name}")),
            };
            self.push_chunk(
                CodeChunk::Code("template_patch_size_be(&state, memo);\n".to_string()),
                Some(format!("End of {tag_name}")),
            );
        }
        self.unindent();
        Ok(())
    }
}
