// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use handler::TransportCommandHandler;
use protocol::Message;
use socket_server::JsonSocketServer;

use crate::app::TransportWrapper;

mod handler;
pub mod protocol;
mod socket_server;

/// Interface for handlers of protocol messages, responding to each message with a single
/// instance of the same protocol message.
pub trait CommandHandler<Msg> {
    fn execute_cmd(&self, msg: &Msg) -> Result<Msg>;
}

/// This is the main entry point for the session proxy.  This struct will either bind on a
/// specified port, or find an available port from a range, before entering an event loop.
pub struct SessionHandler<'a> {
    port: u16,
    socket_server: JsonSocketServer<Message, TransportCommandHandler<'a>>,
}

impl<'a> SessionHandler<'a> {
    pub fn init(transport: &'a TransportWrapper, listen_port: Option<u16>) -> Result<Self> {
        let mut port = listen_port.unwrap_or(9900);
        let limit = listen_port.unwrap_or(9999);
        // Find a suitable port to bind to.
        loop {
            match JsonSocketServer::new(TransportCommandHandler::new(&transport), port) {
                Ok(socket_server) => {
                    // Configure all GPIO pins to default direction and level, according to
                    // configuration files provided.
                    transport.apply_default_pin_configurations()?;
                    return Ok(Self {
                        port,
                        socket_server,
                    });
                }
                Err(e) if port >= limit => bail!(e),
                Err(_) => port += 1,
            }
        }
    }

    pub fn get_port(&self) -> u16 {
        self.port
    }

    pub fn run_loop(&mut self) -> Result<()> {
        self.socket_server.run_loop()
    }
}
