use anyhow::Result;
use erased_serde::Serialize;
use opentitanlib::transport::Transport;
pub use opentitantool_derive::*;

pub mod console;
pub mod hello;

pub trait CommandDispatch {
    fn run(&self, transport: &mut dyn Transport) -> Result<Option<Box<dyn Serialize>>>;
}
