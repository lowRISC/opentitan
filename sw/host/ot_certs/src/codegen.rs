// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module is capable of generating C code for generating a binary X.509
//! certificate according to a [`Template`].

use anyhow::{Context, Result, ensure};
use heck::ToUpperCamelCase;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use std::fmt::Write;

use crate::asn1::codegen::{self, CodegenOutput, VariableCodegenInfo, VariableInfo};
use crate::asn1::x509::X509;
use crate::template::subst::{Subst, SubstData, SubstValue};
use crate::template::vars::ListVariables;
use crate::template::{Payload, SizeRange, Template, Value, Variable, VariableType};
use crate::x509;

/// The amount of test cases to generate for covering more corner cases.
const TEST_CASE_COUNT: u32 = 100;

#[derive(Default)]
pub struct Codegen {
    tmpl_name: String,
    /// Header.
    pub source_h: String,
    /// Code containing the template and setters.
    pub source_c: String,
    /// Code containing the unittest.
    pub source_unittest: String,
}

impl Codegen {
    /// Create a new Codegen builder.
    pub(crate) fn new(tmpl_name: &str) -> Self {
        Self {
            tmpl_name: tmpl_name.to_string(),
            ..Self::default()
        }
    }

    /// Return the formatted builder function name for a component.
    fn builder_name(&self, component: CertificateComponent) -> String {
        format!("{}_build_{}", self.tmpl_name, component.name())
    }

    /// Return the formatted value structure type name for a component.
    fn values_name(&self, component: CertificateComponent) -> String {
        format!("{}_{}_values_t", self.tmpl_name, component.name())
    }

    /// Add license, warning, include guards, and default includes to H, C, and unittest files.
    fn add_boilerplate(&mut self, from_file: &str) -> Result<()> {
        let license_and_warning = generate_license_and_warning(from_file);
        let preproc_guard_include = self.tmpl_name.to_uppercase();

        // Header boilerplate
        self.source_h.push_str(&license_and_warning);
        writeln!(self.source_h, "#ifndef __{}__", preproc_guard_include)?;
        writeln!(self.source_h, "#define __{}__\n", preproc_guard_include)?;
        self.source_h
            .push_str("#include \"sw/device/lib/base/status.h\"\n\n");

        // Source boilerplate
        self.source_c.push_str(&license_and_warning);
        self.source_c.push('\n');
        writeln!(self.source_c, "#include \"{}.h\"", self.tmpl_name)?;
        self.source_c
            .push_str("#include \"sw/device/silicon_creator/lib/cert/asn1.h\"\n\n");
        self.source_c
            .push_str("#include \"sw/device/silicon_creator/lib/cert/template.h\"\n\n");

        // Unittest boilerplate
        self.source_unittest.push_str(&license_and_warning);
        self.source_unittest.push('\n');
        self.source_unittest.push_str("extern \"C\" {\n");
        writeln!(self.source_unittest, "#include \"{}.h\"", self.tmpl_name)?;
        self.source_unittest.push_str("}\n");
        self.source_unittest
            .push_str("#include \"gtest/gtest.h\"\n\n");

        Ok(())
    }

    /// Add a value struct definition to the header file.
    fn add_value_struct(
        &mut self,
        component: CertificateComponent,
        variables: &IndexMap<String, VariableType>,
    ) -> Result<()> {
        let type_name = self.values_name(component);
        let struct_name = type_name.strip_suffix("_t").unwrap();
        writeln!(self.source_h, "typedef struct {struct_name} {{")?;
        for (var_name, var_type) in variables {
            let (_, doc_and_type) = c_variable_info(var_name, "", var_type);
            self.source_h.push_str(&doc_and_type);
        }
        writeln!(self.source_h, "}} {type_name};\n")?;

        if component == CertificateComponent::Certificate {
            // Add type alias for compatibility.
            let compat_type_name = format!("{}_sig_values_t", self.tmpl_name);
            writeln!(self.source_h, "typedef {type_name} {compat_type_name};\n")?;
        }
        Ok(())
    }

    /// Add a builder function (declaration to H, implementation to C).
    /// Returns the BuilderInfo (which contains size info and variables).
    fn add_builder(
        &mut self,
        component: CertificateComponent,
        variables: &IndexMap<String, VariableType>,
        build: impl FnOnce(&mut codegen::Codegen) -> Result<()>,
    ) -> Result<BuilderInfo> {
        let struct_name = self.values_name(component);
        let fn_name = self.builder_name(component);
        let fn_params_str = format!("{struct_name} *values, uint8_t *out_buf, size_t *inout_size");

        let get_var_info = |var_name: &str| -> Result<VariableInfo> {
            let var_type = variables
                .get(var_name)
                .with_context(|| format!("could not find variable '{var_name}'"))
                .copied()?;
            let (codegen, _) = c_variable_info(var_name, "values->", &var_type);
            Ok(VariableInfo { var_type, codegen })
        };

        let fn_impl = codegen::Codegen::generate(
            /* buf_name */ "out_buf",
            /* buf_size_name */ "inout_size",
            &get_var_info,
            build,
        )?;

        let doc = component.fn_doc();
        write!(
            self.source_h,
            r#"
                {doc}
                rom_error_t {fn_name}({fn_params_str});
            "#
        )?;

        let code = &fn_impl.code;
        write!(
            self.source_c,
            r#"
                rom_error_t {fn_name}({fn_params_str}) {{
                  {code}
                  return kErrorOk;
                }}
            "#
        )?;

        Ok(BuilderInfo {
            component,
            variables: variables.clone(),
            output: fn_impl,
        })
    }

    /// Add variable size constants to the header file (wrapped in enum { ... }).
    fn add_variables_constants(
        &mut self,
        variables: &IndexMap<String, VariableType>,
    ) -> Result<()> {
        let tmpl_name = self.tmpl_name.to_upper_camel_case();
        writeln!(self.source_h, "enum {{")?;
        for (var_name, var_type) in variables {
            let (codegen, _) = c_variable_info(var_name, "", var_type);
            let const_name = var_name.to_upper_camel_case();
            let (min_size, max_size) = if let VariableCodegenInfo::Pointer { .. } = codegen {
                let (min_size, max_size) = var_type.array_size();
                if var_type.has_constant_array_size() {
                    writeln!(
                        self.source_h,
                        "  k{tmpl_name}Exact{const_name}SizeBytes = {max_size},"
                    )?;
                }
                (min_size, max_size)
            } else {
                (1, 100)
            };
            writeln!(
                self.source_h,
                "  k{tmpl_name}Min{const_name}SizeBytes = {min_size},"
            )?;
            writeln!(
                self.source_h,
                "  k{tmpl_name}Max{const_name}SizeBytes = {max_size},"
            )?;
        }
        writeln!(self.source_h, "}};")?;
        Ok(())
    }

    /// Add field name mapping macros to the header file.
    fn add_field_mappings(&mut self, variables: &IndexMap<String, VariableType>) -> Result<()> {
        let tmpl_name = self.tmpl_name.to_upper_camel_case();
        for (var_name, _) in variables {
            let const_name = var_name.to_upper_camel_case();
            writeln!(
                self.source_h,
                "#define k{tmpl_name}Field{const_name} {var_name}"
            )?;
        }
        Ok(())
    }

    /// Add maximum size constant to the header file (wrapped in enum { ... }).
    fn add_max_size_constant(&mut self, info: &BuilderInfo) -> Result<()> {
        let tmpl_name = self.tmpl_name.to_upper_camel_case();
        let component_name = info.component.name().to_upper_camel_case();
        let const_name = format!("k{tmpl_name}Max{component_name}SizeBytes");
        let max_size = info.output.max_size;

        writeln!(self.source_h, "// Maximum possible size")?;
        writeln!(self.source_h, "enum {{")?;
        writeln!(self.source_h, "  {const_name} = {max_size},")?;
        writeln!(self.source_h, "}};")?;
        Ok(())
    }

    /// Append the TEST macro header to unittest.
    fn add_test_header(&mut self, test_name: &str) -> Result<()> {
        let tmpl_name = self.tmpl_name.to_upper_camel_case();
        writeln!(self.source_unittest, "TEST({tmpl_name}, {test_name})\n{{")?;
        Ok(())
    }

    /// Append the closing brace for the test to unittest.
    fn add_test_footer(&mut self) -> Result<()> {
        writeln!(self.source_unittest, "}}\n")?;
        Ok(())
    }

    /// Append C constants for the variable values to unittest.
    fn add_test_constants(&mut self, unittest_data: &SubstData) -> Result<()> {
        for (var_name, data) in &unittest_data.values {
            write!(self.source_unittest, "[[maybe_unused]] ")?;
            match data {
                SubstValue::ByteArray(bytes) => {
                    writeln!(
                        self.source_unittest,
                        "static uint8_t g_{var_name}[] = {{ {} }};",
                        bytes
                            .iter()
                            .map(|x| format!("{:#02x}", x))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )?;
                }
                SubstValue::String(s) => {
                    let s = s.chars().map(|c| format!("'{c}'")).join(", ");
                    writeln!(
                        self.source_unittest,
                        "static char g_{var_name}[] = {{{s}}};"
                    )?
                }
                SubstValue::Uint32(val) => {
                    writeln!(self.source_unittest, "uint32_t g_{var_name} = {val};")?
                }
                SubstValue::Boolean(val) => {
                    writeln!(self.source_unittest, "bool g_{var_name} = {val};")?
                }
            }
        }
        Ok(())
    }

    /// Append expected constant array, size check, debug print, and memcmp check to unittest.
    fn add_test_assertion(
        &mut self,
        data_var: &str,
        size_var: &str,
        expected_bytes: &[u8],
    ) -> Result<()> {
        let temp = data_var.strip_prefix("g_").unwrap_or(data_var);
        let print_name = temp.strip_suffix("_data").unwrap_or(temp);
        write!(
            self.source_unittest,
            r#"
                const uint8_t kExpectedOutput[{}] = {{ {} }};
                EXPECT_EQ({size_var}, sizeof(kExpectedOutput));
                printf("Generated {print_name}: \n");
                for (size_t i = 0; i < {size_var}; ++i) {{
                  printf("%02x, ", {data_var}[i]);
                }}
                printf("\n");
                EXPECT_EQ(0, memcmp({data_var}, kExpectedOutput, {size_var}));
            "#,
            expected_bytes.len(),
            expected_bytes
                .iter()
                .map(|x| format!("0x{:02x}", x))
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        Ok(())
    }

    /// Append C struct variable declaration and assignment for testing.
    fn add_test_values(&mut self, var_name: &str, info: &BuilderInfo) -> Result<()> {
        let type_name = self.values_name(info.component);
        writeln!(self.source_unittest, "{type_name} {var_name} = {{")?;
        for (var_name, var_type) in &info.variables {
            let (codegen, _) = c_variable_info(var_name, "", var_type);
            match codegen {
                VariableCodegenInfo::Pointer {
                    ptr_expr,
                    size_expr,
                } => {
                    writeln!(self.source_unittest, "  .{ptr_expr} = g_{var_name},")?;
                    if !var_type.has_constant_array_size() {
                        writeln!(
                            self.source_unittest,
                            "  .{size_expr} = sizeof(g_{var_name}),"
                        )?;
                    }
                }
                VariableCodegenInfo::Uint32 { value_expr }
                | VariableCodegenInfo::Boolean { value_expr } => {
                    writeln!(self.source_unittest, "  .{value_expr} = g_{var_name},")?;
                }
            }
        }
        writeln!(self.source_unittest, "}};")?;
        Ok(())
    }

    /// Append C buffer declaration, size initialization, builder call and size checks to unittest.
    fn add_test_builder_call(
        &mut self,
        values_var: &str,
        data_var: &str,
        size_var: &str,
        info: &BuilderInfo,
    ) -> Result<()> {
        let max_size = info.output.max_size;
        let min_size = info.output.min_size;
        let builder_fn = self.builder_name(info.component);

        write!(
            self.source_unittest,
            r#"
                uint8_t {data_var}[{max_size}];
                size_t {size_var} = sizeof({data_var});
                EXPECT_EQ(kErrorOk, {builder_fn}(&{values_var}, {data_var}, &{size_var}));
                EXPECT_GE({size_var}, {min_size});
                EXPECT_LE({size_var}, {max_size});
            "#
        )?;
        Ok(())
    }

    /// Finalize the code generation (e.g., closing include guards).
    fn finalize(&mut self) -> Result<()> {
        let preproc_guard_include = self.tmpl_name.to_uppercase();
        writeln!(
            self.source_h,
            "\n#endif /* __{}__ */",
            preproc_guard_include
        )?;
        Ok(())
    }
}

/// Generate the certificate template header and source file.
///
/// The generated files will indicate that they have been automatically
/// generated from `from_file`.
/// Returns the implementation first and the header file second.
/// NOTE: the implementation file will `#include "<header>.h"` the header
/// where `<header>` comes from `tmpl.name`.
///
/// The generated header file contains the following elements. Below `<name>`
/// refers to `tmpl.name` and `<Name>` to the "camel-case" variant of `<name>`.
/// 1. License header, warning, include guard.
/// 2. Relevant includes.
/// 3. Definition of a data structure to hold the values of the variables
///    used in the TBS. It is named `<name>_tbs_values_t`.
/// 4. Definition of a data structure to hold the values of the variables
///    used in the signature. It is named `<name>_sig_values_t`. Note that this
///    structure contains an extra field called `tbs` (and its size `tbs_size`)
///    that must point to the buffer containing the TBS.
/// 5. An enumeration hold two values: one gives the maximum size of the TBS
///    given the variables sizes defined in the template, and another one for
///    the maximum size of the whole certificate. They are named
///    `k<Name>MaxTbsSizeBytes` and `k<Name>MaxCertSizeBytes` respectively.
/// 6. Definition and documentation of a function that takes as input a
///    a `<name>_tbs_values_t` and a buffer to produce the TBS. It is named
///    `<name>_build_tbs` and returns a `rom_error_t`.
/// 7. Definition and documentation of a function that takes as input a
///    a `<name>_sig_values_t` and a buffer to produce the certificate.
///    It is named `<name>_build_cert` and returns a `rom_error_t`.
pub fn generate_source(from_file: &str, tmpl: &Template) -> Result<Codegen> {
    match &tmpl.payload {
        Payload::Certificate { .. } => generate_cert(from_file, tmpl),
        Payload::PrivateExtensions { .. } => generate_private_extensions(from_file, tmpl),
    }
}

/// Generate the certificate template header and source file for a certificate.
pub fn generate_cert(from_file: &str, tmpl: &Template) -> Result<Codegen> {
    let cert = tmpl.certificate()?;
    let mut codegen = Codegen::new(&tmpl.name);
    codegen.add_boilerplate(from_file)?;

    // Partition variables between TBS and signature.
    let mut tbs_var_names = IndexSet::new();
    cert.list_tbs_variables(&mut tbs_var_names);

    let mut sig_var_names = IndexSet::new();
    cert.signature.list_variables(&mut sig_var_names);

    let mut tbs_vars = IndexMap::<String, VariableType>::new();
    let mut cert_vars = IndexMap::<String, VariableType>::new();

    for (name, var_type) in tmpl.variables.clone() {
        let in_tbs = tbs_var_names.contains(&name);
        let in_sig = sig_var_names.contains(&name);

        ensure!(
            in_tbs || in_sig,
            "variable '{name}' is declared in variables but never used in the certificate"
        );

        if in_tbs {
            tbs_vars.insert(name.clone(), var_type);
        }
        if in_sig {
            cert_vars.insert(name, var_type);
        }
    }

    // Structure containing the TBS variables.
    codegen.add_value_struct(CertificateComponent::Tbs, &tbs_vars)?;

    // Generate TBS function.
    let tbs_info = codegen.add_builder(CertificateComponent::Tbs, &tbs_vars, |builder| {
        X509::push_tbs_certificate(builder, cert)
    })?;

    // Create a special variable to hold the TBS binary.
    let tbs_binary_val_name = "tbs";
    cert_vars.insert(
        tbs_binary_val_name.to_string(),
        VariableType::ByteArray {
            size: SizeRange::RangeSize(tbs_info.output.min_size, tbs_info.output.max_size),
            tweak_msb: None,
        },
    );
    let tbs_binary_val = Value::Variable(Variable {
        name: tbs_binary_val_name.to_string(),
        convert: None,
    });

    // Structure containing the signature variables.
    codegen.add_value_struct(CertificateComponent::Certificate, &cert_vars)?;

    // Generate sig function.
    let cert_info =
        codegen.add_builder(CertificateComponent::Certificate, &cert_vars, |builder| {
            X509::push_certificate(builder, &tbs_binary_val, &cert.signature)
        })?;

    // Create constants for the variable size range.
    let all_vars = tbs_vars
        .iter()
        .chain(cert_vars.iter())
        .unique_by(|(name, _)| *name)
        .map(|(k, v)| (k.clone(), *v))
        .collect::<IndexMap<_, _>>();
    codegen.add_variables_constants(&all_vars)?;
    codegen.add_field_mappings(&all_vars)?;

    codegen.add_max_size_constant(&cert_info)?;

    // Generate unittest.
    for idx in 0..TEST_CASE_COUNT {
        generate_cert_test_case(
            &mut codegen,
            &format!("Verify{idx}"),
            &tbs_info,
            &cert_info,
            tmpl,
        )?;
    }

    codegen.finalize()?;
    Ok(codegen)
}

/// Generate the certificate template header and source file for private extensions only.
pub fn generate_private_extensions(from_file: &str, tmpl: &Template) -> Result<Codegen> {
    let private_extensions = tmpl.private_extensions()?;
    let mut codegen = Codegen::new(&tmpl.name);
    codegen.add_boilerplate(from_file)?;

    // Structure containing the extension variables.
    codegen.add_value_struct(CertificateComponent::PrivateExtList, &tmpl.variables)?;

    // Generate Extensions function.
    let ext_info = codegen.add_builder(
        CertificateComponent::PrivateExtList,
        &tmpl.variables,
        |builder| {
            for ext in private_extensions {
                X509::push_cert_extension(builder, ext)?
            }
            Ok(())
        },
    )?;

    codegen.add_variables_constants(&tmpl.variables)?;
    codegen.add_field_mappings(&tmpl.variables)?;

    codegen.add_max_size_constant(&ext_info)?;

    // Generate unittest.
    for idx in 0..TEST_CASE_COUNT {
        generate_exts_test_case(
            &mut codegen,
            &format!("VerifyExtList{idx}"),
            &ext_info,
            tmpl,
        )?;
    }

    codegen.finalize()?;
    Ok(codegen)
}

// Generate a unit test test case with random variables.
fn generate_cert_test_case(
    codegen: &mut Codegen,
    test_name: &str,
    tbs_info: &BuilderInfo,
    cert_info: &BuilderInfo,
    tmpl: &Template,
) -> Result<()> {
    let min_tbs_size = tbs_info.output.min_size;
    let max_tbs_size = tbs_info.output.max_size;

    let unittest_data = tmpl.random_test()?;
    let expected_cert = x509::generate_certificate(&tmpl.subst(&unittest_data)?)?;

    codegen.add_test_header(test_name)?;

    // Generate constants holding the data.
    codegen.add_test_constants(&unittest_data)?;

    // Generate structure to hold the TBS data and call builder.
    codegen.add_test_values("g_tbs_values", tbs_info)?;
    codegen.add_test_builder_call("g_tbs_values", "g_tbs", "tbs_size", tbs_info)?;

    // Generate structure to hold the certificate data.
    codegen.add_test_values("g_cert_values", cert_info)?;

    // Extra setup for Cert: set tbs_size.
    if min_tbs_size != max_tbs_size {
        writeln!(
            codegen.source_unittest,
            "  g_cert_values.tbs_size = tbs_size;"
        )?;
    }

    // Call Cert builder.
    codegen.add_test_builder_call("g_cert_values", "g_cert_data", "cert_size", cert_info)?;

    codegen.add_test_assertion("g_cert_data", "cert_size", &expected_cert)?;

    codegen.add_test_footer()?;

    Ok(())
}

// Generate a unit test test case with random variables for extensions only template.
fn generate_exts_test_case(
    codegen: &mut Codegen,
    test_name: &str,
    ext_info: &BuilderInfo,
    tmpl: &Template,
) -> Result<()> {
    let unittest_data = tmpl.random_test()?;
    let expected_exts = x509::generate_private_extensions(&tmpl.subst(&unittest_data)?)?;

    codegen.add_test_header(test_name)?;

    // Generate constants holding the data.
    codegen.add_test_constants(&unittest_data)?;

    // Generate structure to hold the extension data.
    codegen.add_test_values("g_ext_values", ext_info)?;
    codegen.add_test_builder_call("g_ext_values", "g_exts", "exts_size", ext_info)?;

    codegen.add_test_assertion("g_exts", "exts_size", &expected_exts)?;

    codegen.add_test_footer()?;

    Ok(())
}

struct BuilderInfo {
    component: CertificateComponent,
    variables: IndexMap<String, VariableType>,
    output: CodegenOutput,
}

#[derive(Debug, PartialEq, Copy, Clone)]
enum CertificateComponent {
    Certificate,
    Tbs,
    PrivateExtList,
}

impl CertificateComponent {
    fn name(&self) -> &'static str {
        match self {
            Self::Tbs => "tbs",
            Self::Certificate => "cert",
            Self::PrivateExtList => "private_ext",
        }
    }

    fn fn_doc(&self) -> &'static str {
        match self {
            Self::Tbs => {
                r#"/**
 * Generates a TBS certificate.
 *
 * @param values Pointer to a structure giving the values to use to generate the TBS
 * portion of the certificate.
 * @param[out] out_buf Pointer to a user-allocated buffer that will contain the TBS portion of
 * the certificate.
 * @param[in,out] inout_size Pointer to an integer holding the size of
 * the provided buffer; this value will be updated to reflect the actual size of
 * the output.
 * @return The result of the operation.
 */"#
            }
            Self::Certificate => {
                r#"/**
 * Generates an endorsed certificate from a TBS certificate and a signature.
 *
 * @param values Pointer to a structure giving the values to use to generate the
 * certificate (TBS and signature).
 * @param[out] out_buf Pointer to a user-allocated buffer that will contain the
 * result.
 * @param[in,out] inout_size Pointer to an integer holding the size of
 * the provided buffer, this value will be updated to reflect the actual size of
 * the output.
 * @return The result of the operation.
 */"#
            }
            Self::PrivateExtList => {
                r#"/**
 * Generates the private extension list.
 *
 * @param values Pointer to a structure giving the values to use to generate the extensions.
 * @param[out] out_buf Pointer to a user-allocated buffer that will contain the result.
 * @param[in,out] inout_size Pointer to an integer holding the size of
 * the provided buffer; this value will be updated to reflect the actual size of
 * the output.
 * @return The result of the operation.
 */"#
            }
        }
    }
}

// Decide whether a integer should use a special C type instead
// of being represented by a big-endian byte array.
fn c_integer_for_length(size: usize) -> Option<&'static str> {
    match size {
        4 => Some("uint32_t"),
        _ => None,
    }
}

// Return information about a variable (codegen info, definition in struct).
fn c_variable_info(
    name: &str,
    struct_expr: &str,
    var_type: &VariableType,
) -> (VariableCodegenInfo, String) {
    match var_type {
        VariableType::ByteArray { .. } => {
            if var_type.has_constant_array_size() {
                (
                    VariableCodegenInfo::Pointer {
                        ptr_expr: format!("{struct_expr}{name}"),
                        size_expr: format!("{}", var_type.size()),
                    },
                    indoc::formatdoc! {r#"
                        // Pointer to an array of bytes.
                        uint8_t *{name};
                    "#
                    },
                )
            } else {
                (
                    VariableCodegenInfo::Pointer {
                        ptr_expr: format!("{struct_expr}{name}"),
                        size_expr: format!("{struct_expr}{name}_size"),
                    },
                    indoc::formatdoc! {r#"
                        // Pointer to an array of bytes.
                        uint8_t *{name};
                        // Size of this array in bytes.
                        size_t {name}_size;
                    "#
                    },
                )
            }
        }
        VariableType::Integer { .. } => match c_integer_for_length(var_type.size()) {
            Some(c_type) => (
                VariableCodegenInfo::Uint32 {
                    value_expr: format!("{struct_expr}{name}"),
                },
                format!("    {c_type} {name};\n"),
            ),
            None => {
                if var_type.has_constant_array_size() {
                    (
                        VariableCodegenInfo::Pointer {
                            ptr_expr: format!("{struct_expr}{name}"),
                            size_expr: format!("{}", var_type.size()),
                        },
                        indoc::formatdoc! {r#"
                            // Pointer to an unsigned big-endian in integer.
                            uint8_t *{name};
                        "#
                        },
                    )
                } else {
                    (
                        VariableCodegenInfo::Pointer {
                            ptr_expr: format!("{struct_expr}{name}"),
                            size_expr: format!("{struct_expr}{name}_size"),
                        },
                        indoc::formatdoc! {r#"
                            // Pointer to an unsigned big-endian in integer.
                            uint8_t *{name};
                            // Size of this array in bytes.
                            size_t {name}_size;
                        "#
                        },
                    )
                }
            }
        },
        VariableType::String { .. } => {
            if var_type.has_constant_array_size() {
                (
                    VariableCodegenInfo::Pointer {
                        ptr_expr: format!("{struct_expr}{name}"),
                        size_expr: format!("{}", var_type.size()),
                    },
                    indoc::formatdoc! {r#"
                        // Pointer to a (not necessarily zero-terminated) string.
                        char *{name};
                    "#
                    },
                )
            } else {
                (
                    VariableCodegenInfo::Pointer {
                        ptr_expr: format!("{struct_expr}{name}"),
                        size_expr: format!("{struct_expr}{name}_len"),
                    },
                    indoc::formatdoc! {r#"
                        // Pointer to a (not necessarily zero-terminated) string.
                        char *{name};
                        // Length of this string.
                        size_t {name}_len;
                    "#
                    },
                )
            }
        }
        VariableType::Boolean => (
            VariableCodegenInfo::Boolean {
                value_expr: format!("{struct_expr}{name}"),
            },
            format!("bool {name};\n"),
        ),
        VariableType::Selector { .. } => (
            VariableCodegenInfo::Uint32 {
                value_expr: format!("{struct_expr}{name}"),
            },
            format!("    uint32_t {name};\n"),
        ),
    }
}

fn generate_license_and_warning(from_file: &str) -> String {
    indoc::formatdoc! { r#"
    // Copyright lowRISC contributors (OpenTitan project).
    // Licensed under the Apache License, Version 2.0, see LICENSE for details.
    // SPDX-License-Identifier: Apache-2.0

    // This file was automatically generated using opentitantool from:
    // {from_file}
    "#}
}
