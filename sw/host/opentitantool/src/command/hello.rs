// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Sample command heirarchy.
//!
//! This module implements a sample command heirarchy to demonstrate
//! the command framework for opentitantool.

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;

#[derive(Debug, Args)]
/// The `hello world` command accepts an command option of `--cruel`.
pub struct HelloWorld {
    #[arg(short, long)]
    cruel: bool,
}

#[derive(serde::Serialize)]
/// The [`HelloMessage`] is the result of the `hello world` command.
pub struct HelloMessage {
    pub greeting: String,
}

impl CommandDispatch for HelloWorld {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // Is the world cruel or not?
        let msg = if self.cruel {
            "Hello cruel World!"
        } else {
            "Hello World!"
        };
        Ok(Some(Box::new(HelloMessage {
            greeting: msg.to_owned(),
        })))
    }
}

#[derive(Debug, Args)]
/// The `hello people` command takes no additional switches or arguments.
pub struct HelloPeople;

impl CommandDispatch for HelloPeople {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        // The `hello people` command produces no result.
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// There are two types of `hello` subcommand; this enum binds them together
/// so they can both be under the `hello` command.  This enum also derives
/// `CommandDispatch` which automatically builds a `run` method for this
/// type which dispatches to the subcommands.
pub enum HelloTypes {
    World(HelloWorld),
    People(HelloPeople),
}

#[derive(Debug, Args)]
/// The `goodbye` command takes no options or arguments.
pub struct GoodbyeCommand {}

#[derive(serde::Serialize)]
/// The [`GoodbyeMessage`] is the result of the `goodbye` command.
pub struct GoodbyeMessage {
    pub message: String,
}

impl CommandDispatch for GoodbyeCommand {
    fn run(
        &self,
        _context: &dyn Any,
        _transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        Ok(Some(Box::new(GoodbyeMessage {
            message: "Goodbye!".to_owned(),
        })))
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
/// The [`Greetings`] enum binds the `hello` and `goodbye` command hirarchies
/// in this module together into a single type which can be included into
/// the root of the command heirarchy in `main.rs`.
pub enum Greetings {
    #[command(subcommand)]
    Hello(HelloTypes),
    Goodbye(GoodbyeCommand),
}
