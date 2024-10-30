// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::fs::{self, File};
use std::io::Write;
use std::path::PathBuf;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use ot_certs::template::subst::{Subst, SubstData};
use ot_certs::template::Template;
use ot_certs::CertFormat;
use ot_certs::{codegen, x509};

fn load_template(path: &PathBuf) -> Result<Template> {
    // Load template.
    let template_content = fs::read_to_string(path)
        .with_context(|| format!("Could not load the template file {}", path.display()))?;
    Template::from_hjson_str(&template_content)
        .with_context(|| format!("Failed to parse template file {}", path.display()))
}

fn load_subst(path: &PathBuf) -> Result<SubstData> {
    let data_content = fs::read_to_string(path)
        .with_context(|| format!("Could not load the data file {}", path.display()))?;
    SubstData::from_json(&data_content)
        .with_context(|| format!("Failed to parse data file {}", path.display()))
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
    /// Substitute values in a template.
    Subst(SubstCommand),
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
    /// Output file for C++ unittest.
    #[arg(long)]
    output_unittest: Option<PathBuf>,
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

        if let Some(output_unittest) = &self.output_unittest {
            let mut output_unittest = File::create(output_unittest)?;
            writeln!(output_unittest, "{}", codegen.source_unittest)?;
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
    /// Optional substitution data.
    #[arg(long)]
    subst: Option<PathBuf>,
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
        // Load data.
        let data = self.subst.as_ref().map(load_subst).transpose()?;
        // Warn user if there is no substitution data and variables.
        if !template.variables.is_empty() && data.is_none() {
            bail!("the template contains variable so you must specify some substition data using --subst")
        }
        // Substitute
        let template = if let Some(data) = data {
            template.subst(&data)?
        } else {
            template
        };
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

#[derive(Debug, Args)]
pub struct SubstCommand {
    /// Filename of the input hjson template.
    template: PathBuf,
    /// Filename to the substitution data.
    subst: PathBuf,
    /// Filename of the output hjson template.
    #[arg(long)]
    output: Option<PathBuf>,
}

impl CommandDispatch for SubstCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Load template.
        let template = load_template(&self.template)?;
        // Load data.
        let data = load_subst(&self.subst)?;
        // Substitute
        let template = template.subst(&data)?;
        // Output
        if let Some(output) = &self.output {
            let mut file = File::create(output)?;
            let doc = serde_annotate::serialize(&template)?.to_hjson().to_string();
            writeln!(file, "{}", doc)?;
        }
        Ok(Some(Box::new(template)))
    }
}
