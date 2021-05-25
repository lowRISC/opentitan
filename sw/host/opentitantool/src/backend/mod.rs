use anyhow::Result;
use structopt::StructOpt;
use thiserror::Error;

use opentitanlib::transport::{EmptyTransport, Transport};

pub mod verilator;

#[derive(Debug, StructOpt)]
pub struct BackendOpts {
    #[structopt(long, default_value)]
    interface: String,

    #[structopt(flatten)]
    verilator_opts: verilator::VerilatorOpts,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("unknown interface {0}")]
    UnknownInterface(String),
}

/// Creates the requested backend interface according to [`BackendOpts`].
pub fn create(args: &BackendOpts) -> Result<Box<dyn Transport>> {
    match args.interface.as_str() {
        "" => Ok(Box::new(EmptyTransport::new())),
        "verilator" => verilator::create(&args.verilator_opts),
        _ => Err(Error::UnknownInterface(args.interface.clone()).into()),
    }
}
