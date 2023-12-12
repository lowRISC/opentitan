// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use clap::{Args, Subcommand, ValueEnum};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use ot_certs::template::Template;
use ot_certs::{codegen, x509};

fn load_template(path: &PathBuf) -> Result<Template> {
    // Load template.
    let template_content = fs::read_to_string(path)
        .with_context(|| format!("Could not load the template file {}", path.display()))?;
    Template::from_hjson_str(&template_content)
        .with_context(|| format!("Failed to parse template file {}", path.display()))
}

/// Commands for interacting with certificates.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum CertificateCommand {
    /// Generate a binary certificate
    Generate(GenCertCommand),
    /// Generate code for a certificate template.
    Codegen(CodegenCommand),
    /// Parse a certificate.
    Parse(ParseCertificate),
}

/// Generate a certificate template.
#[derive(Clone, Debug, ValueEnum)]
pub enum CertFormat {
    X509,
}

/// Generate a certificate template.
#[derive(Debug, Args)]
pub struct CodegenCommand {
    /// Filename of the template.
    #[arg(long)]
    template: PathBuf,
    /// Certificate format
    #[arg(long, value_enum, default_value_t = CertFormat::X509)]
    cert_format: CertFormat,
    /// Output directory path.
    #[arg(long, required_unless_present_any(["output_c", "output_h"]))]
    output_dir: Option<PathBuf>,
    /// Output file for C source.
    #[arg(long, required_unless_present = "output_dir")]
    output_c: Option<PathBuf>,
    /// Output file for H header.
    #[arg(long, required_unless_present = "output_dir")]
    output_h: Option<PathBuf>,
    /// Output file for writer C source (optional).
    #[arg(long)]
    output_writer: Option<PathBuf>,
    /// Output file for test file (optional).
    #[arg(long)]
    output_tests: Option<PathBuf>,
}

impl CommandDispatch for CodegenCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let template = load_template(&self.template)?;
        // Generate C and header files.
        let (output_c, output_h) = if let Some(output_dir) = &self.output_dir {
            (
                output_dir.join(format!("{}.c", &template.name)),
                output_dir.join(format!("{}.h", &template.name)),
            )
        } else {
            (
                self.output_c
                    .clone()
                    .expect("--output-c must be specified when --output-dir is not used"),
                self.output_h
                    .clone()
                    .expect("--output-h must be specified when --output-dir is not used"),
            )
        };
        let mut output_c = File::create(output_c)?;
        let mut output_h = File::create(output_h)?;

        let codegen = codegen::generate_cert(&self.template.display().to_string(), &template)?;
        writeln!(output_c, "{}", codegen.source_c)?;
        writeln!(output_h, "{}", codegen.source_h)?;

        // Output writer.
        if let Some(output_writer) = &self.output_writer {
            let mut output_writer = File::create(output_writer)?;
            writeln!(output_writer, "{}", codegen.writer)?;
        }
        // Generate test vectors
        if let Some(output_tests) = &self.output_tests {
            let tests = template.gen_tests()?;
            let mut output_tests = File::create(output_tests)?;
            writeln!(output_tests, "{}", tests.to_json()?)?;
        }

        Ok(None)
    }
}

/// Generate a certificate.
#[derive(Debug, Args)]
pub struct GenCertCommand {
    /// Filename of the template.
    template: PathBuf,
    /// Certificate format
    #[arg(long, value_enum, default_value_t = CertFormat::X509)]
    cert_format: CertFormat,
    /// Output file.
    output: PathBuf,
}

impl CommandDispatch for GenCertCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Load template.
        let template = load_template(&self.template)?;
        // Check there are no remaining variables.
        if !template.variables.is_empty() {
            let rem_vars = template
                .variables
                .keys()
                .cloned()
                .collect::<Vec<_>>()
                .join(", ");
            bail!("the substition data does not cover the following variables: {rem_vars}")
        }
        // Generate
        let der =
            x509::generate_certificate(&template).context("could not generate X509 certificate")?;
        // Output
        let mut file = File::create(&self.output)?;
        file.write_all(&der)?;

        Ok(None)
    }
}

/// Generate a certificate template.
#[derive(Debug, Args)]
pub struct ParseCertificate {
    /// Filename of the template.
    certificate: PathBuf,
    /// Certificate format
    #[arg(long, value_enum, default_value_t = CertFormat::X509)]
    cert_format: CertFormat,
}

impl CommandDispatch for ParseCertificate {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        let cert = fs::read(&self.certificate).context("could not read certificate from file")?;
        let cert = x509::parse_certificate(&cert)?;
        Ok(Some(Box::new(cert)))
    }
}
